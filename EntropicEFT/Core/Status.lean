import EntropicEFT.Core.Prelude

/-!
# EntropicEFT.Core.Status

LOCAL CONTRACT
* Manuscript: Section 26.
* Status: bookkeeping only.
* Purpose: machine-readable epistemic vocabulary matching the paper.
-/

namespace EntropicEFT

inductive ClaimStatus
  | closed
  | fixed
  | conditional
  | open
  | empirical
  | audit
  | externalMath
  deriving DecidableEq, Repr, Inhabited

structure ClaimRecord where
  id : String
  status : ClaimStatus
  moduleName : String
  manuscript : String
  assumptions : List String
  conclusion : String
  deriving Repr

/-- Exact mathematics can sit downstream of a conditional premise without changing
its mathematical proof status; this mirrors Section 26's ledger discipline. -/
structure ConditionalResult (P Q : Prop) where
  implication : P → Q

end EntropicEFT
