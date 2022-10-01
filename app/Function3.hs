{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-} 
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Function3 where
import FieldAndOther
import Data.IORef
import Text.JSON.Generic
import Data.Sequence as S 

func3 :: Field -> Int -> S.Seq (S.Seq (S.Seq Int)) ->  S.Seq (S.Seq (S.Seq Int)) -> IO (Field)
{-# INLINE func3 #-}
func3 mfield sizeF startPos sBoard = do
    clAd <- clausesAdding mfield
    tAdd <- tMod S.empty
    field <- clAd S.empty
    curCh <- curInd 0
    ffCh <- ffInd 0
    let board = sBoard
    let fI = sequence $ map funcI [1..sizeF] where
        funcI :: Int -> IO [()]
        {-# INLINE funcI #-}
        funcI indexI = sequence $ map funcJ [0..(S.length (startPos `index` indexI) - 1)] where
            funcJ :: Int -> IO ()
            {-# INLINE funcJ #-}
            funcJ indexJ = do
                let newPos = startPos `index` indexI `index` indexJ `index` 2
                let fK = sequence $ map funcK rangeK where
                    rangeK :: [Int]
                    {-# INLINE rangeK #-}
                    rangeK
                        | startPos `index` indexI `index` indexJ `index` 1 == 0 = [(indexI -
                         (columnsF mfield) * (newPos - 1)),
                        (indexI - (columnsF mfield) * (newPos - 2))..indexI]
                        | otherwise = [indexI..(indexI + newPos - 1)]
                    funcK :: Int -> IO ()
                    {-# INLINE funcK #-}
                    funcK indexK = do
                        t <- tAdd S.empty
                        t <- tAdd (S.fromList [-startPos `index` indexI `index` indexJ `index` 0]) 
                        cur <- curCh 0     
                        ff <- ffCh 0
                        t <- tAdd $ S.fromList [0]
                        let fP = sequence $ map funcP [0..(S.length (board `index` indexK) - 1)] where
                            funcP :: Int -> IO ()
                            {-# INLINE funcP #-}
                            funcP indexP = do
                                t <- tAdd $ S.fromList [0] 
                                ff <- ffCh 0
                                cur <- curCh 0
                                t <- tAdd $ S.fromList [0]
                                ff <- ffCh 0
                                cur <- curCh 0
                                if (board `index` indexK `index` indexP `index` 1 /=
                                     startPos `index` indexI `index` indexJ `index` 3) &&
                                      (board `index` indexK `index` indexP `index` 2 /=
                                           startPos `index` indexI `index` indexJ `index` 1) then do
                                    if (t == (S.fromList [-startPos `index` indexI `index` indexJ `index` 0])) ||
                                         (cur == board `index` indexK `index` indexP `index` 1) ||
                                          ((cur /= board `index` indexK `index` indexP `index` 1) &&
                                           (ff == board `index` indexK `index` indexP `index` 3)) then do
                                            t <- tAdd $ S.fromList [0]
                                            t <- tAdd $ S.fromList [board `index` indexK `index` indexP `index` 0]
                                            return ()
                                    else do
                                        t <- tAdd $ S.fromList [0]
                                        field <- clAd t
                                        t <- tAdd S.empty
                                        t <- tAdd $ S.fromList [-startPos `index` indexI `index`
                                         indexJ `index` 0, board `index` indexK `index` indexP `index` 0]
                                        return ()
                                    t <- tAdd $ S.fromList [0]
                                    cur <- curCh $ board `index` indexK `index` indexP `index` 1     
                                    ff <- ffCh $ board `index` indexK `index` indexP `index` 3  
                                    t <- tAdd $ S.fromList [0]
                                    if indexP == (S.length (board `index` indexK) - 1) ||
                                         ((board `index` indexK `index` (indexP + 1) `index` 1 /= cur) &&
                                          (ff /= board `index` indexK `index` (indexP + 1) `index` 3)) then do
                                            t <- tAdd $ S.fromList [0]
                                            field <- clAd t
                                            t <- tAdd S.empty
                                            t <- tAdd $ S.fromList [-startPos `index` indexI `index` indexJ
                                             `index` 0]
                                            return ()
                                    else do
                                        t <- tAdd $ S.fromList [0]
                                        return ()
                                    ff <- ffCh ff
                                    cur <- curCh cur
                                    t <- tAdd $ S.fromList [0]
                                    return ()
                                else do
                                    ff <- ffCh ff
                                    cur <- curCh cur
                                    t <- tAdd $ S.fromList [0]
                                    return ()
                                ff <- ffCh 0
                                cur <- curCh 0
                                t <- tAdd $ S.fromList [0]
                                return ()
                        ffP <- fP
                        return ()
                ffK <- fK
                let fK = sequence $ map funcK rangeK where
                    rangeK :: [Int]
                    {-# INLINE rangeK #-}
                    rangeK
                        | startPos `index` indexI `index` indexJ `index` 1 == 0 =
                             [indexI, (indexI - columnsF field)..1]
                        | otherwise = [indexI..(((indexI - 1) `div` (columnsF field) + 1) * (columnsF field))]
                    funcK :: Int -> IO [()]
                    {-# INLINE funcK #-}
                    funcK indexK = sequence $ map funcT [0..(S.length (startPos `index` indexK) - 1)] where
                        funcT :: Int -> IO ()
                        {-# INLINE funcT #-}
                        funcT indexT = do
                            if (startPos `index` indexK `index` indexT `index` 3 /=
                                 startPos `index` indexI `index` indexJ `index` 3) 
                                && (startPos `index` indexI `index` indexJ `index` 1 ==
                                     startPos `index` indexK `index` indexT `index` 1) 
                                && (startPos `index` indexI `index` indexJ `index` 5 >
                                 startPos `index` indexK `index` indexT `index` 5) 
                                then do
                                    field <- clAd $ S.fromList [-startPos `index` indexI `index` indexJ `index` 0,
                                     -startPos `index` indexK `index` indexT `index` 0]
                                    return ()
                            else do
                                return ()
                            return ()
                ffK <- fK  
                if startPos `index` indexI `index` indexJ `index` 1 == 0 then do
                    if indexI - (columnsF field) * newPos > 0 then do
                        let fK = sequence $ map funcK [0..(S.length (board `index` (indexI - (columnsF field) * newPos)) - 1)] where
                            funcK :: Int -> IO ()
                            {-# INLINE funcK #-}
                            funcK indexK = do
                                if (startPos `index` indexI `index` indexJ `index` 0 - 1) `div` sizeF /=
                                     (board `index` 
                                     (indexI - (columnsF field) * newPos) `index` indexK `index` 0 - 1) `div`
                                      sizeF then do
                                        field <- clAd $ S.fromList [-startPos `index` indexI `index` indexJ
                                         `index` 0, -board `index` (indexI - (columnsF field) * newPos) `index`
                                          indexK `index` 0]
                                        return ()
                                else do
                                    return ()
                                return ()
                        ffK <- fK
                        return ()
                    else do
                        return ()
                    if indexI + (columnsF field) <= sizeF then do
                        let fK = sequence $ map funcK [0..(S.length (board `index` (indexI + columnsF field)) - 1)] where
                            funcK :: Int -> IO ()
                            {-# INLINE funcK #-}
                            funcK indexK = do
                                if (startPos `index` indexI `index` indexJ `index` 0 - 1) `div` sizeF /=
                                     (board `index` (indexI + columnsF field) `index` indexK `index` 0 - 1) `div`
                                      sizeF then do
                                    field <- clAd $ S.fromList [-startPos `index` indexI `index` indexJ `index` 0,
                                     -board `index` (indexI + columnsF field) `index` indexK `index` 0]
                                    return ()
                                else do
                                    return ()
                        ffK <- fK
                        return ()
                    else do
                        return ()
                    return ()
                else do
                    if (indexI - 1) `div` (columnsF field) == (indexI + newPos - 1) `div` (columnsF field) then do
                        let fK = sequence $ map funcK [0..(S.length (board `index` (indexI + newPos)) - 1)] where
                            funcK :: Int -> IO ()
                            {-# INLINE funcK #-}
                            funcK indexK = do
                                if (startPos `index` indexI `index` indexJ `index` 0 - 1) `div` sizeF /=
                                     (board `index` 
                                     (indexI + newPos) `index` indexK `index` 0 - 1) `div` sizeF then do
                                        field <- clAd $ S.fromList [-startPos `index` indexI `index` indexJ
                                         `index` 0, -board `index` (indexI + newPos) `index` indexK `index` 0]
                                        return ()
                                else do
                                    return ()
                                return ()
                        ffK <- fK
                        return ()
                    else do
                        return ()
                    if (indexI - 1) `div` (columnsF field) == (indexI - 2) `div` (columnsF field) then do
                        let fK = sequence $ map funcK [0..(S.length (board `index` (indexI - 1)) - 1)] where
                            funcK :: Int -> IO ()
                            {-# INLINE funcK #-}
                            funcK indexK = do
                                if (startPos `index` indexI `index` indexJ `index` 0 - 1) `div` sizeF /=
                                     (board `index`
                                     (indexI - 1) `index` indexK `index` 0 - 1) `div` sizeF then do
                                        field <- clAd $ S.fromList [-startPos `index` indexI `index` indexJ
                                         `index` 0, -board `index` (indexI - 1) `index` indexK `index` 0]
                                        return ()
                                else do
                                    return ()
                        ffK <- fK
                        return ()
                    else do
                        return ()
                    return ()
                return ()
    ffI <- fI
    field <- clAd S.empty
    return field
 