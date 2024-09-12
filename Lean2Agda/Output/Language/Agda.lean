import Lean2Agda.Output.Language
import Std.Data.HashSet.Basic

open Std (HashSet)

def Agda: Language where
  keywords := HashSet.empty.insertMany [
    "abstract", "codata", "coinductive", "data", "eta-equality", "field",
    "forall", "hiding", "import", "inductive", "infix", "infixl",
    "infixr", "instance", "let", "macro", "module", "mutual",
    "open", "overlap", "pattern", "postulate", "primitive",
    "private", "public", "quote", "quoteContext", "quoteGoal",
    "quoteTerm", "record", "renaming", "rewrite", "syntax",
    "tactic", "unquote", "unquoteDecl", "unquoteDef", "using", "where",
    "with"
  ]
