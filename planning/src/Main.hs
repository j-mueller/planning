{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Main where

import           Control.Lens                                   hiding
                                                                 (children)
import           Control.Monad                                  (foldM)
import           Control.Monad.State
import           Data.Bifunctor                                 (Bifunctor (..))
import           Data.List.NonEmpty                             (NonEmpty (..))
import           Data.Map.Strict                                (Map)
import qualified Data.Map.Strict                                as Map
import           Data.Maybe                                     (catMaybes,
                                                                 fromMaybe)
import           Data.Number.Natural                            (Natural)
import           Data.Ratio                                     (approxRational)
import           Data.Text                                      (Text)
import qualified Data.Text                                      as Text
import           System.Random.MWC                              (GenIO, createSystemRandom)

import           Language.Hakaru.Evaluation.ConstantPropagation (constantPropagation)
import           Language.Hakaru.Evaluation.EvalMonad           (runPureEvaluate)
import qualified Language.Hakaru.Pretty.Concrete                as PC
import qualified Language.Hakaru.Pretty.Haskell                 as PH
import qualified Language.Hakaru.Pretty.Maple                   as PM
import           Language.Hakaru.Sample                         (runEvaluate)
import           Language.Hakaru.Syntax.ABT
import           Language.Hakaru.Syntax.AST                     (Term)
import           Language.Hakaru.Syntax.CSE                     (cse)
import           Language.Hakaru.Syntax.IClasses                (Foldable11 (..))
import qualified Language.Hakaru.Syntax.Prelude                 as Hakaru
import           Language.Hakaru.Syntax.Uniquify                (uniquify)
import           Language.Hakaru.Syntax.Value                   (Value (..))
import           Language.Hakaru.Types.DataKind

import qualified Data.Vector                                    as Vector
import           Text.PrettyPrint                               (Doc, render)

-- | Minimal duration (in days) of a task
minTaskDuration :: Rational
minTaskDuration = 1

main :: IO ()
main = evalGraphModel

-- | Pretty print the `myProject2` model
prettyGraphModel :: IO ()
prettyGraphModel = putStrLn $ prettyDist $ fmap measureDist myProject2

evalGraphModel :: IO ()
evalGraphModel = do
    gen <- createSystemRandom
    smpl <- sampleModel gen myProject2
    mapM_ print smpl
    return ()

-- | Sample the `myProject` model and print out the results
evalTreeModel :: IO ()
evalTreeModel = do
    gen <- createSystemRandom
    smpl <- sampleTask gen myProject
    mapM_ (putStrLn . fmap (\c -> if c == '.' then ',' else c) . show) smpl
    return ()

-- | Approximate the distribution of start and end dates of a set of tasks
sampleModel :: GenIO -> PlannerState Distribution -> IO [[(Double, Double)]]
sampleModel gen ps = do
    let abt :: TrivialABT Term '[] (HMeasure (HArray (HPair HReal HReal))) = modelDist (measureDist <$> ps)
        abt' = runPureEvaluate
                $ constantPropagation
                $ cse
                $ uniquify abt
        warmup = 10000
        sampleSize = 10
        extract :: Vector.Vector (Value (HPair 'HReal 'HReal)) -> [(Double, Double)]
        extract = fmap g . Vector.toList
        g :: Value (HPair 'HReal 'HReal) -> (Double, Double)
        g = \case
            VDatum d -> (\case [l, r] -> (l, r)) $ foldMap11 (\case VReal x -> [x]) d
    case runEvaluate abt' of
        VMeasure f -> do
            let sample1 td i = do
                                r <- f (VProb 1.0) gen
                                if i > warmup
                                then case r of
                                    Nothing             -> return td
                                    Just (VArray r', _) -> return $ extract r':td
                                else return td
            foldM sample1 mempty [1 .. (warmup + sampleSize)]

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

newtype Fix f = Fix { unFix :: f (Fix f) }

hmap :: (Functor f, Functor g) => (forall a. f a -> g a) -> Fix f -> Fix g
hmap e = ana (e . unFix)

ana :: (Functor f) => (a -> f a) -> (a -> Fix f)
ana p = go
    where
    go = Fix . fmap go . p

-- | A task with a duration
data TaskF h d c = TaskF {
    taskName     :: !Text,
    taskDuration :: !d,
    taskDepends  :: h c -- ^ Dependencies
    }
    
instance Functor h => Functor (TaskF h d) where
    fmap f (TaskF n d dd) = TaskF n d (fmap f dd)

class HasTaskF t where
    type ChildTp  t :: * -> *
    type Duration t :: *
    type Children t :: *

    taskF :: Lens' t (TaskF (ChildTp t) (Duration t) (Children t))

    name :: Lens' t Text
    name = taskF . lens g s where
        g = taskName
        s tf n = tf { taskName = n }

    duration :: Lens' t (Duration t)
    duration = taskF . lens g s where
        g = taskDuration
        s tf d = tf { taskDuration = d }

    children :: Lens' t (ChildTp t (Children t))
    children = taskF . lens g s where
        g = taskDepends
        s tf d = tf { taskDepends = d }

instance HasTaskF (TaskF h d c) where
    type ChildTp  (TaskF h d c) = h
    type Duration (TaskF h d c) = d
    type Children (TaskF h d c) = c

    taskF = id

instance Functor h => Bifunctor (TaskF h) where
    bimap f g (TaskF n d dd) = TaskF n (f d) (g <$> dd)

newtype Task d = Task { getTask :: Fix (TaskF [] d) }

instance Functor Task where
    fmap f (Task t) = Task (hmap (first f) t)

-- | Create a task with a list of subtasks
mkTask :: Text -> d -> [Task d] -> Task d
mkTask t d = Task . Fix . TaskF t d . fmap getTask

-- | Get the parameters of a normal distribution from a confidence interval
distribution :: TwoSigmaInterval -> Distribution
distribution (TwoSigmaInterval l u) = NormalDist m s where
    m = (l + u) / 2
    s = (u - m) / 2

constantDuration :: Rational -> Distribution
constantDuration = DiracDist

-- | Turn a distribution into a Hakaru measure
measureDist :: ABT Term abt => Distribution -> abt '[] (HMeasure HReal)
measureDist (NormalDist m s) = Hakaru.max mn Hakaru.<$> Hakaru.normal m' s' where
    m' = Hakaru.real_ m
    s' = Hakaru.unsafeProb $ Hakaru.real_ s
    mn = Hakaru.real_ minTaskDuration
measureDist (DiracDist a) = Hakaru.dirac $ Hakaru.real_ a

-- | Create a distribution from the 95% (2 sigma) confidence interval
approxIntvl :: Rational -> Rational -> Distribution
approxIntvl a = distribution . TwoSigmaInterval a

-- | Create a task whose duration
task :: Text -> Distribution -> Task Distribution
task t dist = mkTask t dist []

-- | Create a group with tasks that can run in parallel
taskGroup :: Text -> [Task Distribution] -> Task Distribution
taskGroup t = mkTask t (constantDuration 0)

-- | Chain two tasks so that the second task can only start after the
--   first one has finished.
andThen :: Task Distribution -> Task Distribution -> Task Distribution
andThen (Task a) (Task (Fix (TaskF t d ch))) = Task (Fix (TaskF t d (a:ch)))

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
        mkTask "subtask 6" (approxIntvl 5 20) [
            task "subtask 6-1" (approxIntvl 3 20),
            task "subtask 6-2" (approxIntvl 5 10)
            ]
        ]

-- | Get the total duration of task including dependencies
taskDist :: ABT Term abt
    => Task (abt '[] (HMeasure HReal))
    -> abt '[] (HMeasure HReal)
taskDist (Task (Fix (TaskF _ m ch))) =
    let
        mn = Hakaru.real_ minTaskDuration
        m' = Hakaru.max mn Hakaru.<$> m in
    case ch of
    [] -> m'
    xs -> let a = Hakaru.arrayLit (taskDist . Task <$> xs)
              d = Hakaru.reduce (Hakaru.liftM2 Hakaru.max) (Hakaru.dirac mn) a
          in  d Hakaru.>>= (\d' -> (d' Hakaru.+) Hakaru.<$> m')

----------------
-- WIP
-- The definitions below are for a new model that allows multiple tasks to
-- depend on the same task (ie. a DAG instead of the tree we have in `Task a`)
---------------

newtype TaskId = TaskId { getTaskId :: Int }
    deriving (Eq, Ord, Show)

-- | Useful information about a task
data TaskMeta = TaskMeta {
    taskMetaName        :: !Text,
    taskMetaDescription :: !Text
    }

data PlannerState a = PlannerState {
    plannerStateDurations    :: Map TaskId a, -- ^ The duration of each task
    plannerStateDependencies :: Map TaskId (Dependency TaskId), -- ^ Dependencies of a task
    plannerStateMetaData     :: Map TaskId TaskMeta,
    plannerStateIDs          :: [TaskId] -- ^ Supply of task IDs
    } deriving Functor

durations :: Lens (PlannerState a) (PlannerState b) (Map TaskId a) (Map TaskId b)
durations = lens g s where
    g = plannerStateDurations
    s ps d = ps { plannerStateDurations = d }

dependencies :: Lens' (PlannerState a) (Map TaskId (Dependency TaskId))
dependencies = lens g s where
    g = plannerStateDependencies
    s ps d = ps { plannerStateDependencies = d }

initialPlannerState :: PlannerState a
initialPlannerState = PlannerState d dd md i where
    d = Map.empty
    dd = Map.empty
    md = Map.empty
    i = TaskId <$> [0..] -- NB: It is important the task IDs start with 0 and taks are continuously numbered (without gaps) because these IDs will be used as array indices later on (FIXME)

type PlannerMonad = State (PlannerState Distribution)

newtype Task' = Task' { getTask' :: TaskF Dependency Distribution TaskId }

instance HasTaskF Task' where
    type ChildTp Task'  = Dependency
    type Duration Task' = Distribution
    type Children Task' = TaskId

    taskF = lens getTask' (const Task')

data Dependency a =
    AllOf [Dependency a]
    | AnyOf [Dependency a]
    | Dep a
    deriving Functor

-- | Create a [[Task']] with a list of subtasks
mkTask' :: Text -> Distribution -> Dependency TaskId -> Task'
mkTask' t d = Task' . TaskF t d

-- | Create a [[Task']] whose duration is given by a distribution
task' :: Text -> Distribution -> Task'
task' t dist = mkTask' t dist (AllOf [])

-- | Create a group of [[Task']]s that can run in parallel
taskGroup' :: Text -> [TaskId] -> Task'
taskGroup' t = mkTask' t (constantDuration 0) . AnyOf . fmap Dep

-- | Get a fresh ID
nextID :: MonadState (PlannerState a) m => m TaskId
nextID = do
    s <- get
    let x:xs = plannerStateIDs s
    put $ s { plannerStateIDs = xs }
    return x

-- | Add a task to the planner state
addTask' :: MonadState (PlannerState Distribution) m
    => Task'
    -> m TaskId
addTask' t = do
    i <- nextID
    _ <- durations . at i ?= (t ^. duration)
    _ <- dependencies . at i ?= (t ^. children)
    return i

-- | Generate a probabilistic model from a planner state, assigning to each task
--   its begin and end date.
modelDist :: forall (abt :: [Hakaru] -> Hakaru -> *). ABT Term abt
    => PlannerState (abt '[] (HMeasure HReal))
    -> abt '[] (HMeasure (HArray (HPair HReal HReal)))
modelDist PlannerState{ plannerStateDurations = du , plannerStateDependencies = de } = inner ms where
    ids = Map.keys du
    durations = Map.toAscList du
    dists = snd <$> durations

    -- An array of functions that compute the start date of each task given an array of task durations
    startDates :: abt '[] (HArray (HArray HReal :-> HReal))
    startDates = Hakaru.arrayLit
                    $ Hakaru.lam . flip lkp . fst
                    <$> Map.toAscList de

    -- Given an array of task durations, compute the earliest start date of a task
    -- based on its dependencies
    -- TODO: Dynamic programming to avoid recursion!
    lkp :: abt '[] (HArray HReal) -> TaskId -> abt '[] HReal
    lkp arr i = 
        let ll a = arr Hakaru.! Hakaru.nat_ (fromIntegral $ getTaskId a)
            go r = case r of
                        Dep a    -> lkp arr a Hakaru.+ ll a
                        AnyOf [] -> Hakaru.zero -- no dependencies; can start immediately
                        AnyOf xs -> let x':xs' = go <$> xs
                                    in foldl Hakaru.min x' xs'
                        AllOf [] -> Hakaru.zero -- no dependencies; can start immediately
                        AllOf xs -> let x':xs' = go <$> xs
                                    in foldl Hakaru.max x' xs'
        in maybe Hakaru.zero go $ Map.lookup i de
                    

    -- Generate a measure of the durations of all tasks from the input distributions
    ms :: abt '[] (HMeasure (HArray HReal))
    ms = foldl go (Hakaru.dirac Hakaru.empty) dists where
        go ms' x = ms' Hakaru.>>= (\ms'' -> ((\x' -> Hakaru.appendV ms'' (Hakaru.arrayLit [x']) ) Hakaru.<$> x))

    -- Apply `toDates` to the measure of task durations
    inner :: abt '[] (HMeasure (HArray HReal)) -> abt '[] (HMeasure (HArray (HPair HReal HReal)))
    inner x = toDates Hakaru.<$> x

    -- Turn an array of task durations into an array of pairs (begin, end) (ie. absolute dates)
    toDates :: abt '[] (HArray HReal) -> abt '[] (HArray (HPair HReal HReal))
    toDates durs = Hakaru.mapWithIndex (f durs) durs

    -- Given an array of task durations, and the index and duration of a specific task, compute the start
    -- and end date of that task.
    f :: abt '[] (HArray HReal) -> abt '[] HNat -> abt '[] HReal -> abt '[] (HPair HReal HReal)
    f durs idx dur =
        let ds = startDates Hakaru.! idx
            startDate = Hakaru.app ds durs
        in Hakaru.pair startDate (startDate Hakaru.+ dur)

prettyDist ::
       PlannerState (TrivialABT Term '[] ('HMeasure 'HReal))
    -> String
prettyDist = p . opt . modelDist where
    -- opt = cse . runPureEvaluate . constantPropagation . uniquify
    opt = id
    p = render . PH.pretty
    -- p = render PC.pretty
    -- p = PM.pretty

-- | Example project
myProject2 :: PlannerState Distribution
myProject2 = snd $ flip runState initialPlannerState $ do
    a <- addTask' $ task' "a" (approxIntvl 10 20)
    b <- addTask' $ task' "b" (approxIntvl 10 20)
    -- c and d start at the same time, when a or b are finished
    c  <- addTask' $ mkTask' "c" (approxIntvl 5 8) (AnyOf [Dep a, Dep b])
    d  <- addTask' $ mkTask' "d" (approxIntvl 10 12) (AnyOf [Dep a, Dep b])
    -- e starts when c and d are finished
    _ <- addTask' $ mkTask' "e" (approxIntvl 2 3) (AllOf [Dep c, Dep d])
    return ()
