module Elfe.Verifier where

import Control.Applicative                                   
import Control.Exception
import Control.Monad                                   

import Debug.Trace

import Elfe.Language
import Elfe.Prover


verify problem = verSeq problem (Context [] Empty) (return Correct)

verStat :: Statement -> Context -> IO ProofStatus
verStat (Statement id f Assumed) context = trace ("Assume " ++ id ++ ": " ++ show f) return Correct 
verStat (Statement id f ByContext) context = trace ("Prove  " ++ id ++ ": " ++ show f) checkStat (Statement id f ByContext) context 
verStat (Statement id f (BySubcontext ids)) context = trace ("Prove  " ++ id ++ ": " ++ show f ++ " by " ++ concat ids) checkStat (Statement id f ByContext) $ restrictContext context ids
verStat (Statement id f (BySequence sequ)) context = trace ("Check  " ++ id ++ ": " ++ show f) verSeq sequ (Context [] context) (return Correct) 
verStat (Statement id f (BySplit split)) context = trace ("Split  " ++ id ++ ": " ++ show f) verifySplit split context (return Correct)

verSeq :: [Statement] -> Context -> IO ProofStatus -> IO ProofStatus
verSeq [] _ status = status
verSeq (st:sts) (Context hs p) status = do
  r <- verStat st (Context hs p)
  if r == Correct then verSeq sts (Context (hs ++ [st]) p) status 
  else verSeq sts (Context (hs ++ [st]) p) (return Incorrect)

checkStat :: Statement -> Context -> IO ProofStatus
checkStat (Statement id formula p) context = prove (show context ++ "fof(" ++ id ++ ", conjecture, (" ++ show formula ++ ")).\n") --return Correct

verifySplit :: [Statement] -> Context -> IO ProofStatus -> IO ProofStatus
verifySplit [] context status = status 
verifySplit (c:cs) context status = do
  r <- verStat c context
  if r == Correct then verifySplit cs context status 
  else verifySplit cs context (return Incorrect)

