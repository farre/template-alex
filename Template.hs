{-# Language TemplateHaskell, RecordWildCards #-}
module Template where

import Alex

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

import Language.Haskell.Meta.Parse ( parseExp )

templateDriver :: Driver [Q Dec] (Q Exp)
templateDriver = Driver {..}
  where
    startCodesHeader ls = foldr (.) id [
      ((typeDec n):) .
      ((funDec n c):)
      | (n, c) <- ls
      ] []
      where
        typeDec n = sigD (mkName n) (conT ''Int)
        funDec n c = funD (mkName n) [clause [] (normalB [| c |]) []]

    actions ls = [ funDec n c | (n, c) <- ls ]
      where
        funDec n c = funD (mkName n) [clause [] (normalB c) []]

    tables t ub vs = [ funD name [clause [] body []] ]
      where
        name = mkName (tableName t)
        body = normalB (appsE [varE (mkName "listArray"),
                               [| (0,ub) |],
                               [| vs |]])

    accepts t ub = (tables t ub) . (map outputAccs)
      where
         outputAccs = appsE . go
           where
             go []
               = [conE (mkName "AlexAccNone")]
             go (Acc _ Nothing Nothing NoRightContext : [])
               = [conE (mkName "AlexAccSkip")]
             go (Acc _ (Just act) Nothing NoRightContext : [])
               = [conE (mkName "AlexAcc"), act]
             go (Acc _ Nothing lctx rctx : rest)
               = [conE (mkName "AlexAccSkipPred"),
                  outputPred lctx rctx,
                  (appsE (go rest))]
             go (Acc _ (Just act) lctx rctx : rest)
               = [conE (mkName "AlexAccPred"), act,
                  outputPred lctx rctx, (appsE (go rest))]

             outputPred (Just set) NoRightContext
               = outputLCtx set
             outputPred Nothing rctx
               = outputRCtx rctx
             outputPred (Just set) rctx
               = infixApp (outputLCtx set)
                          (varE (mkName ("alexAndPred")))
                          (outputRCtx rctx)

             outputLCtx set = appsE [varE (mkName ("alexPrevCharMatches")),
                                     charSetQuote set]

             outputRCtx NoRightContext = [| error "This shouldn't happen" |]
             outputRCtx (RightContextRExp sn)
               = appsE [varE (mkName "alexRightContext"), lift sn]
             outputRCtx (RightContextCode code)
               = expression code

             charSetQuote :: CharSet -> ExpQ
             charSetQuote s = newName "c" >>= \c ->
               lam1E (varP c) $
                     foldr (\x y -> infixApp x orE y) falseE
                           (map (quoteRange (varE c)) (rSetRanges s))
               where
                 andE = [| (&&) |]
                 orE  = [| (||) |]
                 gtE  = [| (>) |]
                 ltE  = [| (<) |]
                 lteE = [| (<=) |]
                 gteE = [| (>=) |]
                 falseE = [| False |]
                 trueE  = [| True |]
                 quoteRange c (Range l h) = infixApp (quoteL c l) andE (quoteH c h)
                 quoteL c (BoundaryAbove a) = infixApp c gtE (lift a)
                 quoteL c (BoundaryBelow a) = infixApp c gteE (lift a)
                 quoteL c (BoundaryAboveAll) = falseE
                 quoteL c (BoundaryBelowAll) = trueE
                 quoteH c (BoundaryAbove a) = infixApp c lteE (lift a)
                 quoteH c (BoundaryBelow a) = infixApp c ltE (lift a)
                 quoteH c (BoundaryAboveAll) = trueE
                 quoteH c (BoundaryBelowAll) = falseE

    expression = (either error return) . parseExp

instance Lift e => Lift (Q e) where
  lift e = e >>= lift

instance Lift Exp where
  lift = return

test = runIO $ do
  f <- readFile "simple.x"
  case parse f of
    Left (_, str) -> return []
    Right (h, ds, s, f) -> do
     let (scanner_final, scs, ds) = processScanner templateDriver s
     ds' <- runQ (sequence ds)

     let dfa = scanner2dfa Latin1 scanner_final scs
         min_dfa = minimizeDFA dfa
         nm  = scannerName scanner_final

     ts <- runQ (sequence (outputDFA templateDriver 1 nm min_dfa))

     return $ ds' ++ ts

alex = QuasiQuoter {
  quoteDec
   = \ str ->
     case parse str of
       Left (_, str) -> error str
       Right (h, ds, s, f) -> do
         let (scanner_final, scs, ds) = processScanner templateDriver s
         ds' <- sequence ds

         let dfa = scanner2dfa Latin1 scanner_final scs
             min_dfa = minimizeDFA dfa
             nm  = scannerName scanner_final

         ts <- sequence (outputDFA templateDriver 1 nm min_dfa)

         return $ ds' ++ ts
}
