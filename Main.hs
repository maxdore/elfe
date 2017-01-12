data Problem = [Sentence] Conjecture
data Result = Proof | Disproof | Unknown

verify :: Text -> [Result]
verify text = map verifySection text  

verifySection :: Section -> [Result]
verifySection section = map     

prove :: Problem -> Result