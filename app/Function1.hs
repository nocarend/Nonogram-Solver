{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-} 
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Function1 where
import Data.Sequence as S
import FieldAndOther
func1 :: Field -> Int -> S.Seq Int -> Int -> S.Seq (S.Seq (S.Seq Int)) -> Int -> S.Seq (S.Seq (S.Seq Int))
 -> IO (Field, S.Seq (S.Seq (S.Seq Int)), S.Seq (S.Seq (S.Seq Int)), Int)
{-# INLINE func1 #-}
func1 mfield nol layers sizeF sP stInd sBoard = do
    clAd <- clausesAdding mfield
    spAdd <- sPing sP
    plInd <- incrInd stInd
    bAdd <- boarding sBoard
    tAdd <- tMod S.empty
    field <- clAd S.empty
    startPos <- spAdd 0 S.empty
    ind <- plInd 0
    board <- bAdd 0 S.empty
    let st1 = mfunc where
        mfunc :: IO ()
        {-# INLINE mfunc #-}
        mfunc = do
            let p = sequence $ map funcI [1..rangeI] where
                rangeI :: Int
                {-# INLINE rangeI #-}
                rangeI 
                    | nol == 1 = rowsF mfield 
                    | otherwise = columnsF mfield
                funcI :: Int -> IO [()]
                {-# INLINE funcI #-}
                funcI indexI = sequence $ map funcJ [1..(S.length ((rangeJ (horF mfield) (verF mfield))
                 `index` indexI) - 1)] where
                    rangeJ :: S.Seq (S.Seq Int) -> S.Seq (S.Seq Int) -> S.Seq (S.Seq Int)
                    {-# INLINE rangeJ #-}
                    rangeJ lenH lenV
                        | nol == 1 = lenV
                        | otherwise = lenH
                    funcJ :: Int -> IO ()
                    {-# INLINE funcJ #-}
                    funcJ indexJ = do
                        let cur = 2 * indexJ - nol
                        t <- tAdd S.empty
                        let funcK = sequence $ map inK rangeK where 
                            rangeK :: [Int]
                            {-# INLINE rangeK #-}
                            rangeK 
                                | nol == 1 = [(layers `index` cur + (indexI - 1) * (columnsF mfield) + 1)..
                                (layers `index` cur + indexI * (columnsF mfield) + 1 - (verF mfield) `index`
                                 indexI `index` indexJ)]
                                | otherwise = [(layers `index` (cur + 1)) - columnsF mfield + indexI, ((layers
                                 `index` (cur + 1)) - 2 * (columnsF mfield) + indexI)..(layers `index` cur +
                                  indexI + ((((horF mfield) `index` indexI) `index` indexJ) - 1) * (columnsF mfield))]
                            inK :: Int -> IO ()
                            {-# INLINE inK #-}
                            inK indexK = do
                                t <- tAdd $ S.fromList [indexK]
                                let l1 = goodMod indexK sizeF
                                ind <- plInd 0
                                let pep = spAdd l1 $ S.fromList [indexK, nol, mas `index` indexI `index` indexJ, ind, indexI, indexJ] where-- 
                                    mas :: S.Seq (S.Seq Int)
                                    {-# INLINE mas #-}
                                    mas 
                                        | nol == 1 = verF mfield
                                        | otherwise = horF mfield
                                startPos <- pep
                                let st2 = sequence $ map funcP rangeP where
                                    rangeP :: [Int]
                                    {-# INLINE rangeP #-}
                                    rangeP 
                                        | nol == 1 = [indexK..(indexK + (verF mfield `index` indexI)
                                         `index` indexJ - 1)]
                                        | otherwise = [indexK, (indexK - columnsF mfield)..(indexK -
                                         (((horF mfield) `index` indexI) `index` 
                                        indexJ) * (columnsF mfield) + 1)]
                                    funcP :: Int -> IO ()
                                    {-# INLINE funcP #-}
                                    funcP indexP = do
                                        let l1 = goodMod indexP sizeF
                                        board <- bAdd l1 $ S.fromList [indexK, ind, nol, indexI, indexJ] 
                                        return ()
                                sst <- st2
                                return ()
                        kFunc <- funcK
                        ind <- plInd 1
                        t <- tAdd $ S.fromList [0]
                        let s1 = sequence $ map funcS1 [0..(S.length t - 1)] where 
                            funcS1 :: Int -> IO ()
                            {-# INLINE funcS1 #-}
                            funcS1 indexS1 = do
                                let s2 = sequence $ map funcS2 [(indexS1 + 1)..(S.length t - 1)] where
                                    funcS2 :: Int -> IO ()
                                    {-# INLINE funcS2 #-}
                                    funcS2 indexS2 = do
                                        let tt = [-(t `index` indexS1), -(t `index` indexS2)]
                                        field <- clAd $ S.fromList tt
                                        return ()
                                ss2 <- s2
                                return ()
                        ss1 <- s1
                        field <- clAd t
                        return ()
            ppp <- p
            return ()
    kkkk <- st1
    ind <- plInd 0
    startPos <- spAdd 0 S.empty
    board <- bAdd 0 S.empty
    field <- clAd S.empty
    return (field, startPos, board, ind)