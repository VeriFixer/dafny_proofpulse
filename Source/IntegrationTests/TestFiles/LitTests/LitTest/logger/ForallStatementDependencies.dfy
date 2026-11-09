// RUN: %baredafny verify --log-format:text --isolate-assertions --boogie -trackVerificationCoverage "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// The conclusion of a forall statement is a proof dependency of the proofs that use it.
// CHECK: Results for ProofForm \(correctness\)
// CHECK:       ForallStatementDependencies.dfy\(26,11\)-\(26,54\): this postcondition holds
// CHECK:     Proof dependencies:
// CHECK:       ForallStatementDependencies.dfy\(26,11\)-\(26,54\): ensures clause
// CHECK:       ForallStatementDependencies.dfy\(29,13\)-\(29,29\): forall statement conclusion
// CHECK: Results for CallForm \(correctness\)
// CHECK:       ForallStatementDependencies.dfy\(37,11\)-\(37,46\): this postcondition holds
// CHECK:     Proof dependencies:
// CHECK:       ForallStatementDependencies.dfy\(37,11\)-\(37,46\): ensures clause
// CHECK:       ForallStatementDependencies.dfy\(40,5\)-\(40,11\): call

function F(n: nat): nat { if n == 0 then 0 else F(n - 1) + 1 }

// Needs induction, which the solver does not do on its own.
lemma {:induction false} FId(n: nat)
  ensures F(n) == n
{
  if n > 0 { FId(n - 1); }
}

// Proof form: only the forall statement proves the postcondition.
lemma ProofForm(k: nat)
  ensures forall n: nat :: n < k ==> F(n) + 1 == n + 1
{
  forall n: nat | n < k
    ensures F(n) + 1 == n + 1
  {
    FId(n);
  }
}

// Call form: only the forall call proves the postcondition.
lemma CallForm(k: nat)
  ensures forall n: nat :: n < k ==> F(n) == n
{
  forall n: nat | n < k {
    FId(n);
  }
}
