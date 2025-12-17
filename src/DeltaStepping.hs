{-# LANGUAGE RecordWildCards  #-}
--
-- INFOB3CC Concurrency
-- Practical 2: Single Source Shortest Path
--
--    Δ-stepping: A parallelisable shortest path algorithm
--    https://www.sciencedirect.com/science/article/pii/S0196677403000762
--
-- https://ics.uu.nl/docs/vakken/b3cc/assessment.html
--
-- https://cs.iupui.edu/~fgsong/LearnHPC/sssp/deltaStep.html
--

module DeltaStepping (

  Graph, Node, Distance,
  deltaStepping,

) where

import Sample
import Utils

import Control.Concurrent
import Control.Concurrent.MVar
import Control.Monad
import Data.Bits
import Data.Graph.Inductive                                         ( Gr )
import Data.IORef
import Data.IntMap.Strict                                           ( IntMap )
import Data.IntSet                                                  ( IntSet )
import Data.Vector.Storable                                         ( Vector )
import Data.Word
import Foreign.Ptr
import Foreign.Storable
import Text.Printf
import qualified Data.Graph.Inductive                               as G
import qualified Data.IntMap.Strict                                 as Map
import qualified Data.IntSet                                        as Set
import qualified Data.Vector.Mutable                                as V
import qualified Data.Vector.Storable                               as S ( unsafeFreeze )
import qualified Data.Vector.Storable.Mutable                       as S


type Graph    = Gr String Distance  -- Graphs have nodes labelled with Strings and edges labelled with their distance
type Node     = Int                 -- Nodes (vertices) in the graph are integers in the range [0..]
type Distance = Float               -- Distances between nodes are (positive) floating point values


-- | Find the length of the shortest path from the given node to all other nodes
-- in the graph. If the destination is not reachable from the starting node the
-- distance is 'Infinity'.
--
-- Nodes must be numbered [0..]
--
-- Negative edge weights are not supported.
--
-- NOTE: The type of the 'deltaStepping' function should not change (since that
-- is what the test suite expects), but you are free to change the types of all
-- other functions and data structures in this module as you require.
--
deltaStepping
    :: Bool                             -- Whether to print intermediate states to the console, for debugging purposes
    -> Graph                            -- graph to analyse
    -> Distance                         -- delta (step width, bucket width)
    -> Node                             -- index of the starting node
    -> IO (Vector Distance)
deltaStepping verbose graph delta source = do
  threadCount <- getNumCapabilities             -- the number of (kernel) threads to use: the 'x' in '+RTS -Nx'

  -- Initialise the algorithm
  (buckets, distances)  <- initialise graph delta source
  printVerbose verbose "initialse" graph delta buckets distances

  let
    -- The algorithm loops while there are still non-empty buckets
    loop = do
      done <- allBucketsEmpty buckets
      if done
      then return ()
      else do
        printVerbose verbose "result" graph delta buckets distances
        step verbose threadCount graph delta buckets distances
        loop
  loop

  printVerbose verbose "result" graph delta buckets distances
  -- Once the tentative distances are finalised, convert into an immutable array
  -- to prevent further updates. It is safe to use this "unsafe" function here
  -- because the mutable vector will not be used any more, so referential
  -- transparency is preserved for the frozen immutable vector.
  --
  -- NOTE: The function 'Data.Vector.convert' can be used to translate between
  -- different (compatible) vector types (e.g. boxed to storable)
  --
  S.unsafeFreeze distances

-- Initialise algorithm state
--
initialise
    :: Graph
    -> Distance
    -> Node
    -> IO (Buckets, TentativeDistances)
initialise graph delta source = do
  let n = G.order graph

  tentDistances <- S.replicate n infinity
  S.write tentDistances source 0.0 --source is the index of the starting node so we can write this index as 0.0

  let weights = [w | (_, _, w) <- G.labEdges graph]
      numBuckets = ceiling (maximum weights / delta) + 1 --FUTURE ME: ADD BUFFER IF STUFF BREAKS

  bucketsArray <- V.replicate numBuckets Set.empty --every bucket starts as IntSet.empty except for bucket 0 which has the start node
  V.write bucketsArray 0 (Set.singleton source)
  startRef <- newIORef 0

  return (Buckets { firstBucket = startRef, bucketArray = bucketsArray }, tentDistances)

-- cabal run exe:delta-stepping-test -- -p "bench"
-- Take a single step of the algorithm.
-- That is, one iteration of the outer while loop.
--
step
    :: Bool
    -> Int
    -> Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
step verbose threadCount graph delta buckets distances = do
  -- In this function, you need to implement the body of the outer while loop,
  -- which contains another while loop.
  -- See function 'deltaStepping' for inspiration on implementing a while loop
  -- in a functional language.
  -- For debugging purposes, you may want to place:
  --   printVerbose verbose "inner step" graph delta buckets distances
  -- in the inner loop.
  firstBucketIndex <- findNextBucket buckets
  let arr = bucketArray buckets

  let
    -- The algorithm loops while there are still non-empty buckets
    loop r = do
      printVerbose verbose "inner step" graph delta buckets distances
      bucket <- V.read arr firstBucketIndex
      if bucket == Set.empty
        then return r
        else do
          requestsLight <- findRequests threadCount (<=delta) graph bucket distances
          let r' = Set.union r bucket
          V.write arr firstBucketIndex Set.empty

          relaxRequests threadCount buckets distances delta requestsLight

          loop r'

  rFinal <- loop Set.empty
  requestsHeavy <- findRequests threadCount (>delta) graph rFinal distances
  relaxRequests threadCount buckets distances delta requestsHeavy

-- Once all buckets are empty, the tentative distances are finalised and the
-- algorithm terminates.
--
allBucketsEmpty :: Buckets -> IO Bool
allBucketsEmpty buckets = go 0
  where
    array = bucketArray buckets

    n = V.length array

    go i
      | i >= n    = return True
      | otherwise = do
          curBucket <- V.read array i
          if curBucket == Set.empty
            then go (i+1)
            else return False
  --The array is a vector with a pointer to a bucket. Buckets are IntSets containing the nodes in the bucket.
  --To loop over them, we need to check for every pointer if they point to an empty bucket


-- Return the index of the first non-empty bucket. Assumes that there is at
-- least one non-empty bucket remaining.
--
findNextBucket :: Buckets -> IO Int --TODO: has to be cyclic. Not literally first empty bucket. --Later Comment: actually this works. I dont know why but im not gonna questioin it. Later later comment: alright turns out my linear implementation was quirky. It DOES solve all testcases, but it does not respect the logic of deltastepping. It just picks the first empty bucket of the physical array, instead of treating it as cyclic. Weird that it still solves everything. Anyway, after implementing the following cyclic array it now solves 3x faster.
findNextBucket buckets = do
  first <- readIORef (firstBucket buckets) --for example, index 6. Search from index 6 and loop back around
  go first
  where
    array = bucketArray buckets
    n = V.length array

    go i = do
      let i' = i `rem` n
      curBucket <- V.read array i'
      if curBucket == Set.empty
        then go (i+1)
        else do
          writeIORef (firstBucket buckets) i
          return i'


-- Create requests of (node, distance) pairs that fulfil the given predicate
--
findRequests
    :: Int
    -> (Distance -> Bool)
    -> Graph
    -> IntSet
    -> TentativeDistances
    -> IO (IntMap Distance)
findRequests threadCount p graph v' distances = do --FOR FUTURE ME: split the nodeList in an equal amount just like with IBAN and just let every thread do exactly this function. Afterwards union all their answers with a minimum for doubles.

  resultArray <- V.replicate threadCount Map.empty

  forkThreads threadCount (worker resultArray)

  maps <- forM [0 .. threadCount - 1] $ \i -> V.read resultArray i

  return (Map.unionsWith min maps)

  where
    nodeList = Set.toList v'
    chunks = splitList threadCount nodeList

    worker :: V.IOVector (IntMap Distance) -> Int -> IO ()
    worker resultArray index = do
      when (index < length chunks) $ do
          result <- handle (chunks !! index)
          let threadMap = Map.fromListWith min result
          threadMap `seq` V.write resultArray index threadMap --needs to evaluate here because in my initial implementation i just wrote to the resultArray. This didnt speed anything up though because it was just a thunk so the execution speed was the same as one thread.

      where
        handle :: [Int] -> IO [(Node, Distance)]
        handle threadList = do
          foldM (\acc node -> do 
            distance_v <- S.read distances node
            let edges = G.out graph node

            let filteredEdges = [edge | edge@(_, _, distance) <- edges, p distance]
            let newDistance = [(neighbour, distance_v + distance) | (_, neighbour, distance) <- filteredEdges]

            return (newDistance ++ acc)
            ) [] threadList

  -- We now have a complete list of all nodes reachable from the bucket. Some might be shorter or longer than others, so we need to filter out. Above foldM can be parallilised(?)
  --
splitList :: Int -> [a] -> [[a]]
splitList _ [] = []
splitList n list = a : (splitList (n-1) b)
  where
    size = (length list + n - 1) `div` n
    (a, b) = splitAt size list
-- Execute requests for each of the given (node, distance) pairs
--
relaxRequests
    :: Int
    -> Buckets
    -> TentativeDistances
    -> Distance
    -> IntMap Distance
    -> IO ()
relaxRequests threadCount buckets distances delta req = do
  --IntMap distances (req) is een koppeling van een node aan een MOGELIJKE distance.
  --Voor elke request moeten we kijken of de distance lager is dan de echte distance, en als dat zo is updaten
  let chunks = splitList threadCount (Map.toList req)

  forkThreads threadCount (worker chunks)

  where
    worker :: [[(Set.Key, Distance)]] -> Int -> IO ()
    worker chunks index = when (index < length chunks) $ do
      forM_ (chunks !! index) $ relax buckets distances delta

  -- rip:
  -- i made this at first and then realized this was exactly the same as this one liner: forM_ (Map.toList req) $ relax buckets distances delta
  -- let list = Map.toList req

  -- _ <- recursiveHandle list

  -- return ()
  -- where
  --   recursiveHandle :: [(Set.Key, Distance)] -> IO ()
  --   recursiveHandle [] = return ()
  --   recursiveHandle (x:xs) = do
  --     _ <- handle x
  --     _ <- recursiveHandle xs
  --     return ()

  --   handle :: (Set.Key, Distance) -> IO ()
  --   handle pair@(node, potentialDistance) = do
  --     currentDistance <- S.read distances node
  --     when (potentialDistance < currentDistance) $ relax buckets distances delta pair


-- Execute a single relaxation, moving the given node to the appropriate bucket
-- as necessary
--
relax :: Buckets
      -> TentativeDistances
      -> Distance
      -> (Node, Distance) -- (w, x) in the paper
      -> IO ()
relax buckets distances delta (node, newDistance) = do

  outcome <- atomicModifyIOVectorFloat distances node (\currentDistance ->
    if newDistance < currentDistance
      then (newDistance, Just currentDistance)
      else (currentDistance, Nothing)
    )

  case outcome of
    Nothing -> return () -- No update needed
    Just oldDistance -> do
      -- If the CAS was successful and we updated the distance, we need to move the node to the appropriate bucket.
      -- delete from old bucket
      let newBucketIndex  = floor (newDistance / delta)
      let len             = V.length (bucketArray buckets)

      when (oldDistance /= infinity) $ do
          let oldBucketIndex = floor (oldDistance / delta)
          when (oldBucketIndex /= newBucketIndex) $ do
            _ <- atomicModifyIOVector (bucketArray buckets) (oldBucketIndex `rem` len)
              (\set -> (Set.delete node set, ()))  --delete from old
            return ()

      _ <- atomicModifyIOVector (bucketArray buckets) (newBucketIndex `rem` len)
        (\set -> (Set.insert node set, ()))  --add to new
      return ()


type TentativeDistances = S.IOVector Distance

data Buckets = Buckets
  { firstBucket   :: {-# UNPACK #-} !(IORef Int)           -- real index of the first bucket (j)
  , bucketArray   :: {-# UNPACK #-} !(V.IOVector IntSet)   -- cyclic array of buckets
  }


-- The initial tentative distance, or the distance to unreachable nodes
--
infinity :: Distance
infinity = 1/0


-- Forks 'n' threads. Waits until those threads have finished. Each thread
-- runs the supplied function given its thread ID in the range [0..n).
--
forkThreads :: Int -> (Int -> IO ()) -> IO ()
forkThreads n action = do
  -- Fork the threads and create a list of the MVars which per thread tell
  -- whether the action has finished.
  finishVars <- mapM work [0 .. n - 1]
  -- Once all the worker threads have been launched, now wait for them all to
  -- finish by blocking on their signal MVars.
  mapM_ takeMVar finishVars
  where
    -- Create a new empty MVar that is shared between the main (spawning) thread
    -- and the worker (child) thread. The main thread returns immediately after
    -- spawning the worker thread. Once the child thread has finished executing
    -- the given action, it fills in the MVar to signal to the calling thread
    -- that it has completed.
    --
    work :: Int -> IO (MVar ())
    work index = do
      done <- newEmptyMVar
      _    <- forkOn index (action index >> putMVar done ())  -- pin the worker to a given CPU core
      return done


printVerbose :: Bool -> String -> Graph -> Distance -> Buckets -> TentativeDistances -> IO ()
printVerbose verbose title graph delta buckets distances = when verbose $ do
  putStrLn $ "# " ++ title
  printCurrentState graph distances
  printBuckets graph delta buckets distances
  putStrLn "Press enter to continue"
  _ <- getLine
  return ()

-- Print the current state of the algorithm (tentative distance to all nodes)
--
printCurrentState
    :: Graph
    -> TentativeDistances
    -> IO ()
printCurrentState graph distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+------------\n"
  forM_ (G.labNodes graph) $ \(v, l) -> do
    x <- S.read distances v
    if isInfinite x
       then printf "  %4d  |  %5v  |  -\n" v l
       else printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"
printBuckets
    :: Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
printBuckets graph delta Buckets{..} distances = do
  first <- readIORef firstBucket
  mapM_
    (\idx -> do
      let idx' = first + idx
      printf "Bucket %d: [%f, %f)\n" idx' (fromIntegral idx' * delta) ((fromIntegral idx'+1) * delta)
      b <- V.read bucketArray (idx' `rem` V.length bucketArray)
      printBucket graph b distances
    )
    [ 0 .. V.length bucketArray - 1 ]

-- Print the current bucket
--
printCurrentBucket
    :: Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
printCurrentBucket graph delta Buckets{..} distances = do
  j <- readIORef firstBucket
  b <- V.read bucketArray (j `rem` V.length bucketArray)
  printf "Bucket %d: [%f, %f)\n" j (fromIntegral j * delta) (fromIntegral (j+1) * delta)
  printBucket graph b distances

-- Print a given bucket
--
printBucket
    :: Graph
    -> IntSet
    -> TentativeDistances
    -> IO ()
printBucket graph bucket distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+-----------\n"
  forM_ (Set.toAscList bucket) $ \v -> do
    let ml = G.lab graph v
    x <- S.read distances v
    case ml of
      Nothing -> printf "  %4d  |   -   |  %f\n" v x
      Just l  -> printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"
