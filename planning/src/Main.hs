{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module Main where

import           Control.Monad                                  (foldM)
import           Control.Monad.State
import           Data.Map.Strict                                (Map)
import qualified Data.Map.Strict                                as Map
import           Data.Ratio                                     (approxRational)
import           Data.Text                                      (Text)
import qualified Data.Text                                      as Text
import           System.Random.MWC                              (GenIO, createSystemRandom)

import           Language.Hakaru.Evaluation.ConstantPropagation (constantPropagation)
import           Language.Hakaru.Evaluation.EvalMonad           (runPureEvaluate)
import           Language.Hakaru.Sample                         (runEvaluate)
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST                     (Term)
import           Language.Hakaru.Syntax.CSE                     (cse)
import qualified Language.Hakaru.Syntax.Prelude                 as Hakaru
import           Language.Hakaru.Syntax.Uniquify                (uniquify)
import           Language.Hakaru.Syntax.Value                   (Value (..))
import           Language.Hakaru.Types.DataKind

-- | Minimal duration (in days) of a task
minTaskDuration :: Rational
minTaskDuration = 1

main :: IO ()
main = do
    gen <- createSystemRandom
    smpl <- sampleTask gen myProject
    mapM_ (putStrLn . fmap (\c -> if c == '.' then ',' else c) . show) smpl
    return ()

-- | Approximate the distribution of a task's duration, including its sub tasks
sampleTask :: GenIO -> Task Distribution -> IO [Double]
sampleTask gen task = do
    let abt :: TrivialABT Term '[] ('HMeasure 'HReal) = taskDist (measureDist <$> task)
        abt' = runPureEvaluate
                $ constantPropagation
                $ cse
                $ uniquify abt
        warmup = 1000
        sampleSize = 10000
    case runEvaluate abt' of
        VMeasure f -> do
            let sample1 td i = do
                                r <- f (VProb 1.0) gen
                                if i > warmup
                                then case r of
                                    Nothing            -> return td
                                    Just (VReal r', _) -> return $ r':td
                                else return td
            foldM sample1 mempty [1 .. (warmup + sampleSize)]

data TwoSigmaInterval = TwoSigmaInterval {
    confidenceIntervalLower :: !Rational,
    confidenceIntervalUpper :: !Rational
    }

data Distribution =
    NormalDist { distMean :: !Rational, distSigma :: !Rational }
    | DiracDist { diravVal :: !Rational }

-- | A task with a duration
data Task d = Task {
    taskName     :: !Text,
    taskDuration :: !d,
    taskDepends  :: [Task d] -- ^ Dependencies. Dependencies may run in parallel but they all have to be completed before this task can start.
    }
    deriving Functor

-- | Get the parameters of a normal distribution from a confidence interval
distribution :: TwoSigmaInterval -> Distribution
distribution (TwoSigmaInterval l u) = NormalDist m s where
    m = (l + u) / 2
    s = (u - m) / 2

constantDuration :: Rational -> Distribution
constantDuration = DiracDist

-- | Turn a distribution into a Hakaru measure
measureDist :: ABT Term abt => Distribution -> abt '[] (HMeasure HReal)
measureDist (NormalDist m s) = Hakaru.normal m' s' where
    m' = Hakaru.real_ m
    s' = Hakaru.unsafeProb $ Hakaru.real_ s
measureDist (DiracDist a) = Hakaru.dirac $ Hakaru.real_ a

-- | Create a distribution from the 95% (2 sigma) confidence interval
approxIntvl :: Rational -> Rational -> Distribution
approxIntvl a = distribution . TwoSigmaInterval a

-- | Create a task whose duration
task :: Text -> Distribution -> Task Distribution
task t dist = Task t dist []

-- | Create a group with tasks that can run in parallel
taskGroup :: Text -> [Task Distribution] -> Task Distribution
taskGroup t = Task t (constantDuration 0)

-- | Chain two tasks so that the second task can only start after the
--   first one has finished.
andThen :: Task Distribution -> Task Distribution -> Task Distribution
andThen a (Task t d ch) = Task t d (a:ch)

-- | Example project
myProject :: Task Distribution
myProject = g1 `andThen` g2 `andThen` g3 where
    g1 = taskGroup "G1" [
        task "subtask 1"  (approxIntvl 2 10)
            `andThen` task "subtask 2" (approxIntvl 2 10)
        ]
    g2 = taskGroup "G2" [
        task "subtask 3" (approxIntvl 1 3),
        task "subtask 4" (approxIntvl 2 4)
            `andThen` task "subtask 5" (approxIntvl 5 10)
        ]
    g3 = taskGroup "G3" [
        Task "subtask 6" (approxIntvl 5 20) [
            task "subtask 6-1" (approxIntvl 3 20),
            task "subtask 6-2" (approxIntvl 5 10)
            ]
        ]

-- | Get the total duration of task including dependencies
taskDist :: ABT Term abt => Task (abt '[] (HMeasure HReal)) -> abt '[] (HMeasure HReal)
taskDist (Task _ m ch) =
    let
        mn = Hakaru.real_ minTaskDuration
        m' = Hakaru.max mn Hakaru.<$> m in
    case ch of
    [] -> m'
    xs -> let a = Hakaru.arrayLit (taskDist <$> xs)
              d = Hakaru.reduce (Hakaru.liftM2 Hakaru.max) (Hakaru.dirac mn) a
          in  d Hakaru.>>= (\d' -> (d' Hakaru.+) Hakaru.<$> m')

----------------
-- WIP
-- The definitions below are for a new model that allows multiple tasks to 
-- depend on the same task (ie. a DAG instead of the tree we have in `Task a`)
---------------

newtype TaskId = TaskId Text
    deriving (Eq, Ord, Show)

data TaskDependency a =
    NoDep -- ^ Task that has no dependencies
    | AllOf [a] -- ^ Can start when all of the listed tasks are finished
    | AnyOf [a] -- ^ Can start when at least one of the listed tasks is finished

-- | Useful information about a task
data TaskMeta = TaskMeta {
    taskMetaName        :: !Text,
    taskMetaDescription :: !Text
    }

data PlannerState a = PlannerState {
    plannerStateDurations    :: Map TaskId a, -- ^ The duration of each task
    plannerStateDependencies :: Map TaskId (TaskDependency TaskId), -- ^ Dependencies of a task
    plannerStateMetaData     :: Map TaskId TaskMeta,
    plannerStateIDs          :: [TaskId] -- ^ Supply of task IDs
    }

initialPlannerState :: PlannerState a
initialPlannerState = PlannerState d dd md i where
    d = Map.empty
    dd = Map.empty
    md = Map.empty
    i = TaskId . Text.pack . show <$> [1..]

type PlannerMonad = State (PlannerState Distribution)

-- | Get a fresh ID
nextID :: MonadState (PlannerState a) m => m TaskId
nextID = do
    s <- get
    let x:xs = plannerStateIDs s
    put $ s { plannerStateIDs = xs }
    return x
        