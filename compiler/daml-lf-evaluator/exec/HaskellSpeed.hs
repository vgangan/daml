-- Copyright (c) 2019 The DAML Authors. All rights reserved.
-- SPDX-License-Identifier: Apache-2.0

module HaskellSpeed
  ( main
  ) where

import Data.Time (getCurrentTime,diffUTCTime)

main :: IO ()
main = do
  putStrLn "speed nfib test"
  mapM_ runTest args
    where args = [30..40]
          runTest arg = do stats <- timedNfib arg; print stats

data Stats = Stats
  { func :: String
  , arg :: Int
  , res :: Int
  , duration :: Seconds
  , speed :: Speed } deriving Show

type Seconds = Double
type Speed = Double

timedNfib :: Int -> IO Stats
timedNfib arg = do
  let func = "nfib"
  before <- getCurrentTime
  let !res = nfib arg
  after <- getCurrentTime
  let duration = realToFrac $ diffUTCTime after before
  let speed :: Speed = fromIntegral res / duration
  return $ Stats { func, arg, res, duration, speed }

nfib :: Int -> Int
nfib 0 = 1
nfib 1 = 1
nfib n = nfib (n-1) + nfib (n-2) + 1
