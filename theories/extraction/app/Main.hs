module Main where

import Prelude
import Extraction
import Formulas

instance Show Coq_form where
  show (Var n) = "x" ++ show n
  show (Box f) = "□(" ++ show f ++ ")"
  show (Implies f g) = "(" ++ show f ++ ")→  (" ++ show g ++ ")"
  show (And f g) = "(" ++ show f ++ ") ∧ (" ++ show g ++ ")"
  show (Or f g) = "(" ++ show f ++ ") ∨ (" ++ show g ++ ")"
  show Bot = "⊥"

test_form :: Coq_form
test_form = Implies (Var 0) (Box (Var 1))


main :: IO ()
main = do
  print "Formula : "
  print test_form
  print"A_K"
  print (k_UI 0 test_form)
  print "A_GL"
  print (gl_UI 0 test_form)
  print "A_ISL"
  print (isl_A 0 test_form)
  print "E_ISL"
  print (isl_E 0 test_form)
