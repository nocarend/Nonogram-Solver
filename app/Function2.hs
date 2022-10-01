{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-} 
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Function2 where
import Data.Sequence as S
import FieldAndOther

func2 :: Field -> S.Seq (S.Seq (S.Seq Int)) -> IO (Field)
{-# INLINE func2 #-}
func2 mfield sBoard = do
    clAd <- clausesAdding mfield
    tAdd <- tMod S.empty
    field <- clAd S.empty
    let fI = sequence (map funcI [1..(S.length sBoard - 1)]) where
        funcI :: Int -> IO ()
        {-# INLINE funcI #-}
        funcI indexI = do
            pt <- tAdd S.empty
            pt <- tAdd $ S.fromList [-indexI]
            let fJ = sequence (map funcJ [0..(S.length (sBoard `index` indexI) - 1)]) where
                funcJ :: Int -> IO ()
                {-# INLINE funcJ #-}
                funcJ indexJ = do
                    pt <- tAdd $ S.fromList [sBoard `index` indexI `index` indexJ `index` 0]
                    let t = [indexI, -sBoard `index` indexI `index` indexJ `index` 0]
                    field <- clAd $ S.fromList t
                    return ()
            ffJ <- fJ
            pt <- tAdd $ S.fromList [0]
            field <- clAd pt
            return ()
    ffI <- fI
    field <- clAd S.empty
    return field
