{-# Language QuasiQuotes #-}
module TemplateTest where

import Data.Array
import Data.Char
import Template

import Data.Bits
import Data.Word

import Text.Alex.Wrapper.Monad

[alex|
%wrapper "monad"

@word = [A-Za-z]+

tokens :-

$white+			;

<0> {
   "magic"		{ magic } -- should override later patterns
   ^ @word $		{ both }  -- test both trailing and left context
   @word $		{ eol }  -- test trailing context
   ^ @word		{ bol }  -- test left context
   @word		{ word }
}

<0> \(			{ begin parens }
<parens> [A-Za-z]+	{ parenword }
<parens> \)		{ begin 0 }
|]

data AlexReturn a
  = AlexEOF
  | AlexError  !AlexInput
  | AlexSkip   !AlexInput !Int
  | AlexToken  !AlexInput !Int a

-- alexScan :: AlexInput -> StartCode -> AlexReturn a
alexScan input (sc)
  = alexScanUser undefined input (sc)

alexScanUser user input (sc)
  = case alex_scan_tkn user input (0) input sc AlexNone of
        (AlexNone, input') ->
                case alexGetByte input of
                        Nothing ->
                                   AlexEOF
                        Just _ ->
                                   AlexError input'
        (AlexLastSkip input'' len, _) ->
                AlexSkip input'' len
        (AlexLastAcc k input''' len, _) ->
                AlexToken input''' len k

alex_scan_tkn user orig_input len input s last_acc =
  input `seq` -- strict in the input
  let
        new_acc = (check_accs (alex_accept `quickIndex` (s)))
  in
  new_acc `seq`
  case alexGetByte input of
     Nothing -> (new_acc, input)
     Just (c, new_input) ->
      case fromIntegral c of { (ord_c) ->
        let
                base   = alexIndexInt32OffAddr alex_base s
                offset = (base + ord_c)
                check  = alexIndexInt16OffAddr alex_check offset

                new_s = if (offset >= (0)) && (check == ord_c)
                          then alexIndexInt16OffAddr alex_table offset
                          else alexIndexInt16OffAddr alex_deflt s
        in
        case new_s of
            (-1) -> (new_acc, input)
                -- on an error, we want to keep the input *before* the
                -- character that failed, not after.
            _ -> alex_scan_tkn user orig_input (if c < 0x80 || c >= 0xC0 then (len + (1)) else len)
                                                -- note that the length is increased ONLY if this is the 1st byte in a char encoding)
                        new_input new_s new_acc
      }
  where
        check_accs (AlexAccNone) = last_acc
        check_accs (AlexAcc a  ) = AlexLastAcc a input (len)
        check_accs (AlexAccSkip) = AlexLastSkip  input (len)

        check_accs (AlexAccPred a predx rest)
           | predx user orig_input (len) input
           = AlexLastAcc a input (len)
           | otherwise
           = check_accs rest
        check_accs (AlexAccSkipPred predx rest)
           | predx user orig_input (len) input
           = AlexLastSkip input (len)
           | otherwise
           = check_accs rest


alexPrevCharIs c _ input _ _ = c == alexInputPrevChar input

alexPrevCharMatches f _ input _ _ = f (alexInputPrevChar input)

alexAndPred p1 p2 user in1 len in2
  = p1 user in1 len in2 && p2 user in1 len in2

alexPrevCharIsOneOf arr _ input _ _ = arr ! alexInputPrevChar input

alexRightContext (sc) user _ _ input =
     case alex_scan_tkn user input (0) input sc AlexNone of
          (AlexNone, _) -> False
          _ -> True
        -- TODO: there's no need to find the longest
        -- match when checking the right context, just
        -- the first match will do.

-- used by wrappers

foo = 4

word (p,_,_,input) len = return (take len input)

both (p,_,_,input) len = return ("BOTH:"++ take len input)

eol (p,_,_,input) len = return ("EOL:"++ take len input)

bol (p,_,_,input) len = return ("BOL:"++ take len input)

parenword (p,_,_,input) len = return (map toUpper (take len input))

magic (p,_,_,input) len = return "PING!" -- :: IO String

-- Compile with -funbox-strict-fields for best results!

alexEOF = return "stopped."

scanner str = runAlex str $ do
  let loop = do tok <- alexMonadScan
                if tok == "stopped." || tok == "error."
                        then return [tok]
                        else do toks <- loop
                                return (tok:toks)
  loop


alexMonadScan = do
  inp <- alexGetInput
  sc <- alexGetStartCode
  case alexScan inp sc of
    AlexEOF -> alexEOF
    AlexError ((AlexPn _ line column),_,_,_) -> alexError $ "lexical error at line " ++ (show line) ++ ", column " ++ (show column)
    AlexSkip  inp' len -> do
        alexSetInput inp'
        alexMonadScan
    AlexToken inp' len action -> do
        alexSetInput inp'
        action (ignorePendingBytes inp) len

-- -----------------------------------------------------------------------------
-- Useful token actions

type AlexAction result = AlexInput -> Int -> Alex result

-- just ignore this token and scan another one
-- skip :: AlexAction result
skip input len = alexMonadScan

-- ignore this token, but set the start code to a new value
-- begin :: Int -> AlexAction result
begin code input len = do alexSetStartCode code; alexMonadScan

-- perform an action for this token, and set the start code to a new value
andBegin :: AlexAction result -> Int -> AlexAction result
(action `andBegin` code) input len = do alexSetStartCode code; action input len

token :: (AlexInput -> Int -> token) -> AlexAction token
token t input len = return (t input len)
