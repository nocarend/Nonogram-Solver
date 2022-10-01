{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-} 
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module FieldAndOther where
import Text.JSON.Generic
import Data.IORef
import Data.Sequence as S
import Data.Foldable

data Field = Field {
    rowsF :: Int,
    columnsF :: Int,
    verF :: S.Seq (S.Seq Int),
    horF :: S.Seq (S.Seq Int),
    clausesF :: S.Seq (S.Seq Int)
} deriving (Show, Eq, Ord, Data, Typeable)

clausesAdding :: Field -> IO (S.Seq Int -> IO (Field))
{-# INLINE clausesAdding #-} 
clausesAdding field = do
    r <- newIORef field 
    return (\i -> do
        if S.null i then do
            modifyIORef' r (\l -> l) 
            readIORef r
        else do
            modifyIORef' r (\l -> l {clausesF = (clausesF l) |> i}) 
            readIORef r)

rebuildFieldVer :: Field -> Field
{-# INLINE rebuildFieldVer #-} 
rebuildFieldVer field = field {verF = (toS [[]]) >< (S.mapWithIndex (\i j -> (0 <| j)) (verF field)),
 horF = (toS [[]]) >< (S.mapWithIndex (\i x -> 0 <| (S.reverse x)) (horF field)), 
 rowsF = S.length (verF field), columnsF = S.length (horF field)}

sizeField :: Field -> Int 
{-# INLINE sizeField #-}
sizeField field = (rowsF field) * (columnsF field)

maxRCField :: Field -> Int
{-# INLINE maxRCField #-}
maxRCField field = max (S.foldlWithIndex (\a c b -> max a (S.length b)) 0 (verF field))
 (foldlWithIndex (\a c b -> max a (S.length b)) 0 (horF field))

layersField :: Int -> Int -> S.Seq Int
{-# INLINE layersField #-} 
layersField sizeF maxF= S.fromList $ [sizeF * i | i <- [0..2 * maxF + 1]]

boardField :: Int -> S.Seq (S.Seq (S.Seq Int))
{-# INLINE boardField #-}
boardField sizeF = S.replicate (sizeF + 1) S.empty

startPosField :: Int -> S.Seq (S.Seq (S.Seq Int))
{-# INLINE startPosField #-} 
startPosField sizeF = S.replicate (sizeF + 1) S.empty

toS :: [[Int]] -> S.Seq (S.Seq Int)
{-# INLINE toS #-}
toS l = S.fromList $ map (S.fromList) l

toL :: S.Seq (S.Seq Int) -> [[Int]]
{-# INLINE toL #-}
toL a = toList (mapWithIndex (\i j -> toList j) a)

replace :: Int -> a -> S.Seq a -> S.Seq a
{-# INLINE replace #-}
replace pos newVal seq = (S.take pos seq |> newVal) >< (S.drop (pos + 1) seq)

tMod :: S.Seq Int -> IO (S.Seq Int -> IO (S.Seq Int))
{-# INLINE tMod #-}
tMod t = do
    r <- newIORef t
    return (\i -> do 
        if S.null i then do
             modifyIORef' r (\l -> S.empty)
             readIORef r
        else if index i 0 == 0 then do
            modifyIORef' r (\l -> l)
            readIORef r
        else do
            modifyIORef' r (\l -> l >< i) 
            readIORef r)

incrInd :: Int -> IO (Int -> IO Int)
{-# INLINE incrInd #-} 
incrInd val = do
    r <- newIORef val
    return (\i -> do 
        modifyIORef' r (+ i)
        readIORef r)

curInd :: Int -> IO (Int -> IO Int)
{-# INLINE curInd #-} 
curInd val = do
    r <- newIORef val
    return (\i -> do 
        if i == 0 then do
            modifyIORef' r (\l -> l) 
            readIORef r
        else do
            modifyIORef' r (\l -> i) 
            readIORef r)

ffInd :: Int -> IO (Int -> IO Int)
{-# INLINE ffInd #-} 
ffInd val = do
    r <- newIORef val
    return (\i -> do 
        if i == 0 then do
            modifyIORef' r (\l -> l) 
            readIORef r
        else do
            modifyIORef' r (\l -> i) 
            readIORef r)

sPing :: S.Seq (S.Seq (S.Seq Int)) -> IO (Int -> S.Seq Int -> IO (S.Seq (S.Seq (S.Seq Int)))) 
{-# INLINE sPing #-}
sPing pos = do
    r <- newIORef pos 
    return (\i j -> do 
        if S.null j then do
             modifyIORef' r (\l -> l)
             readIORef r
        else do
            modifyIORef' r (\l -> replace i ((l `index` i) |> j) l) 
            readIORef r)

boarding :: S.Seq (S.Seq (S.Seq Int)) -> IO (Int -> S.Seq Int -> IO (S.Seq (S.Seq (S.Seq Int))))
{-# INLINE boarding #-}
boarding board = do
    r <- newIORef board
    return (\i j -> do
        if S.null j then do
             modifyIORef' r (\l -> l)
             readIORef r
        else do
            modifyIORef' r (\l -> replace i ((l `index` i) |> j) l) 
            readIORef r)

goodMod :: Int -> Int -> Int
{-# INLINE goodMod #-}
goodMod a b
 | a `mod` b == 0 = b
 | otherwise = a `mod` b