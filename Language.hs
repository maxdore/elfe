data Text = [Section]

data Section = Definition | Signature | Axiom | Lemma | Proposition

data Definition = Sentence 
data Signature = Sentence 
data Axiom = Sentence 
data Lemma = Sentence Proof
data Proof = [Sentence]
data Proposition = Sentence 

data Sentence = String


data Term = Const String [Term]
          | Var String

data FOL = Impl FOL FOL
         | Atom String [Term] | Not FOL
         | TT | FF
         | Or FOL FOL | And FOL FOL
         | Exists String FOL | Forall String FOL