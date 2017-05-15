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
verStat (Statement id f Assumed pos) context = do
    traceM ("Assume " ++ id ++ ": " ++ show f)
    return $ StatementStatus id f (Correct (NotProven)) [] pos
verStat (Statement id f ByContext pos) context = do
    traceM ("Prove  " ++ id ++ ": " ++ show f)
    status <- checkStat (Statement id f ByContext pos) context
    return $ StatementStatus id f status [] pos
verStat (Statement id f (BySubcontext ids) pos) context = do
    traceM ("Prove  " ++ id ++ ": " ++ show f ++ " by " ++ concat ids)
    status <- checkStat (Statement id f ByContext pos) $ restrictContext context ids
    return $ StatementStatus id f status [] pos
verStat (Statement id f (BySequence sequ) pos) context = do
    traceM ("Check  " ++ id ++ ": " ++ show f)
    sequStatus <- verSeq sequ (Context [] context) 
    return $ StatementStatus id f (foldStatus sequStatus) sequStatus pos
verStat (Statement id f (BySplit split) pos) context = do
    traceM ("Split  " ++ id ++ ": " ++ show f) 
    splitStatus <- verifySplit split context 
    return $ StatementStatus id f (foldStatus splitStatus) splitStatus pos

checkStat :: Statement -> Context -> IO ProofStatus
checkStat (Statement id formula p _) context = prove (show context ++ "fof(" ++ id ++ ", conjecture, (" ++ show formula ++ ")).\n") 

foldStatus :: [StatementStatus] -> ProofStatus
foldStatus [] = Correct NotProven
foldStatus ((StatementStatus _ _ s _ _):sts) = if isCorrect s
                        then foldStatus sts
                        else Incorrect NotProven

isCorrect :: ProofStatus -> Bool
isCorrect (Correct _) = True
isCorrect _ = False