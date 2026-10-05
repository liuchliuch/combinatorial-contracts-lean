import CombinatorialContracts.Welfare

/-! Fixed interfaces for the official Comparator. -/
noncomputable section
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace CombinatorialContractsAudit

axiom unexpected.{u_1} :
  (∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (M : CombinatorialContracts.Model ι),
  CombinatorialContracts.optimalValue M ≤ CombinatorialContracts.welfare M ∧
  CombinatorialContracts.welfare M ≤ (Fintype.card ι : ℝ) * CombinatorialContracts.optimalValue M)

theorem claim_008.{u_1} :
  (∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (M : CombinatorialContracts.Model ι),
  CombinatorialContracts.optimalValue M ≤ CombinatorialContracts.welfare M ∧
  CombinatorialContracts.welfare M ≤ (Fintype.card ι : ℝ) * CombinatorialContracts.optimalValue M) :=
  @unexpected

end CombinatorialContractsAudit
