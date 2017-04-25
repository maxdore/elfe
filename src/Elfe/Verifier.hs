module Elfe.Verifier where

import Control.Applicative                                   
import Control.Exception
import Control.Monad                                   

import Debug.Trace

import Elfe.Language
import Elfe.Prover

verify :: [Statement] -> IO [StatementStatus]
verify problem = verSeq problem (Context [] Empty)

verSeq :: [Statement] -> Context -> IO [StatementStatus]
verSeq [] _ = return []
verSeq (st:sts) (Context hs p) = do
  status <- verStat st (Context hs p)
  remaining <- verSeq sts (Context (hs ++ [st]) p) 
  return $ status : remaining

verifySplit :: [Statement] -> Context -> IO [StatementStatus]
verifySplit [] _ = return []
verifySplit (c:cs) context = do
  status <- verStat c context
  remaining <- verifySplit cs context 
  return $ status : remaining

verStat :: Statement -> Context -> IO StatementStatus
verStat (Statement id f Assumed) context = 
    trace ("Assume " ++ id ++ ": " ++ show f) return $ StatementStatus id (Correct (ProverName "Assumed")) [] 

verStat (Statement id f ByContext) context = do
    status <- checkStat (Statement id f ByContext) context
    trace ("Prove  " ++ id ++ ": " ++ show f) return $ StatementStatus id status []

verStat (Statement id f (BySubcontext ids)) context = do
    status <- checkStat (Statement id f ByContext) $ restrictContext context ids
    trace ("Prove  " ++ id ++ ": " ++ show f ++ " by " ++ concat ids) return $ StatementStatus id status []

verStat (Statement id f (BySequence sequ)) context = do
    sequStatus <- verSeq sequ (Context [] context) 
    trace ("Check  " ++ id ++ ": " ++ show f) return $ StatementStatus id (Correct (ProverName "TODO")) sequStatus

verStat (Statement id f (BySplit split)) context = do
    splitStatus <- verifySplit split context 
    trace ("Split  " ++ id ++ ": " ++ show f) return $ StatementStatus id (Correct (ProverName "TODO")) splitStatus

checkStat :: Statement -> Context -> IO ProofStatus
checkStat (Statement id formula p) context = prove (show context ++ "fof(" ++ id ++ ", conjecture, (" ++ show formula ++ ")).\n") --return Correct

