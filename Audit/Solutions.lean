import CombinatorialContracts

/-! Fixed interfaces for the official Comparator. -/
noncomputable section
set_option linter.unusedVariables false
open scoped BigOperators Classical
namespace CombinatorialContractsAudit

/-- T1, C3, S16: `CombinatorialContracts.Paper.theorem1`. -/
theorem claim_001.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1)
  (hadd : @CombinatorialContracts.HasAdditiveReward.{u_1} ι inst inst_1 M) (supply : (ι → Real) → Finset.{u_1} ι)
  (hsupply :
    ∀ (p : ι → Real),
      (∀ (i : ι),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (p i)) →
        @CombinatorialContracts.IsSupplyResponse.{u_1} ι inst inst_1 M p (supply p))
  {ε : Real}
  (hε : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
  (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hn :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Fintype.card.{u_1} ι inst)),
  have executed :
    Prod.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind) :=
    @CombinatorialContracts.SupplyProgram.eval.{u_1, u_1} ι (CombinatorialContracts.OracleRun.{u_1} ι) supply
      (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.Model.cost.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.SupplyProgram.algorithm.{u_1} ι inst inst_1 ε);
  have r : CombinatorialContracts.QueryRecord.{u_1} ι :=
    @CombinatorialContracts.OracleRun.output.{u_1} ι
      (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
        executed);
  And
    (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@CombinatorialContracts.QueryRecord.share.{u_1} ι r))
    (And
      (@CombinatorialContracts.IsResponse.{u_1} ι inst inst_1 M (@CombinatorialContracts.QueryRecord.share.{u_1} ι r)
        (@CombinatorialContracts.QueryRecord.response.{u_1} ι r))
      (And
        (@Eq.{1} Real (@CombinatorialContracts.QueryRecord.reward.{u_1} ι r)
          (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
            (@CombinatorialContracts.QueryRecord.response.{u_1} ι r)))
        (And
          (@Eq.{1} Real (@CombinatorialContracts.QueryRecord.utility.{u_1} ι r)
            (@CombinatorialContracts.principal.{u_1} ι inst inst_1 M
              (@CombinatorialContracts.QueryRecord.share.{u_1} ι r)))
          (And
            (@LE.le.{0} Real Real.instLE
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
                (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M))
              (@CombinatorialContracts.principal.{u_1} ι inst inst_1 M
                (@CombinatorialContracts.QueryRecord.share.{u_1} ι r)))
            (And
              (@Membership.mem.{u_1, u_1} (CombinatorialContracts.QueryRecord.{u_1} ι)
                (List.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι))
                (@List.instMembership.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι))
                (@List.cons.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι)
                  (@CombinatorialContracts.OracleRun.initial.{u_1} ι
                    (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed))
                  (@CombinatorialContracts.OracleRun.grid.{u_1} ι
                    (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed)))
                r)
              (And
                (@Eq.{1} Nat
                  (@List.count.{0} CombinatorialContracts.QueryKind
                    (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                      CombinatorialContracts.instDecidableEqQueryKind)
                    CombinatorialContracts.QueryKind.response
                    (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed))
                  (@CombinatorialContracts.OracleRun.responseQueries.{u_1} ι
                    (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed)))
                (And
                  (@LE.le.{0} Real Real.instLE
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@List.count.{0} CombinatorialContracts.QueryKind
                        (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                          CombinatorialContracts.instDecidableEqQueryKind)
                        CombinatorialContracts.QueryKind.response
                        (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                          (List.{0} CombinatorialContracts.QueryKind) executed)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 20)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
                          (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst)))
                        (Real.log
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                      ε))
                  (And
                    (@Eq.{1} Nat
                      (@List.count.{0} CombinatorialContracts.QueryKind
                        (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                          CombinatorialContracts.instDecidableEqQueryKind)
                        CombinatorialContracts.QueryKind.reward
                        (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                          (List.{0} CombinatorialContracts.QueryKind) executed))
                      (@Fintype.card.{u_1} ι inst))
                    (@Eq.{1} Nat
                      (@List.count.{0} CombinatorialContracts.QueryKind
                        (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                          CombinatorialContracts.instDecidableEqQueryKind)
                        CombinatorialContracts.QueryKind.cost
                        (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                          (List.{0} CombinatorialContracts.QueryKind) executed))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))) :=
  @CombinatorialContracts.Paper.theorem1

/-- T1: `CombinatorialContracts.Paper.theorem1_empty`. -/
theorem claim_002.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1)
  (hadd : @CombinatorialContracts.HasAdditiveReward.{u_1} ι inst inst_1 M) (supply : (ι → Real) → Finset.{u_1} ι)
  (hsupply :
    ∀ (p : ι → Real),
      (∀ (i : ι),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (p i)) →
        @CombinatorialContracts.IsSupplyResponse.{u_1} ι inst inst_1 M p (supply p))
  (hn : @Eq.{1} Nat (@Fintype.card.{u_1} ι inst) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (ε : Real),
  have executed :
    Prod.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind) :=
    @CombinatorialContracts.SupplyProgram.eval.{u_1, u_1} ι (CombinatorialContracts.OracleRun.{u_1} ι) supply
      (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.Model.cost.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.SupplyProgram.algorithm.{u_1} ι inst inst_1 ε);
  And
    (@Eq.{1} Real
      (@CombinatorialContracts.QueryRecord.share.{u_1} ι
        (@CombinatorialContracts.OracleRun.output.{u_1} ι
          (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed)))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (And
      (@Eq.{1} Real
        (@CombinatorialContracts.principal.{u_1} ι inst inst_1 M
          (@CombinatorialContracts.QueryRecord.share.{u_1} ι
            (@CombinatorialContracts.OracleRun.output.{u_1} ι
              (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
                executed))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (And
        (@Eq.{1} Real (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (And
          (@Eq.{1} Nat
            (@List.count.{0} CombinatorialContracts.QueryKind
              (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                CombinatorialContracts.instDecidableEqQueryKind)
              CombinatorialContracts.QueryKind.response
              (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
                executed))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (And
            (@Eq.{1} Nat
              (@List.count.{0} CombinatorialContracts.QueryKind
                (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                  CombinatorialContracts.instDecidableEqQueryKind)
                CombinatorialContracts.QueryKind.reward
                (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                  (List.{0} CombinatorialContracts.QueryKind) executed))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Eq.{1} Nat
              (@List.count.{0} CombinatorialContracts.QueryKind
                (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                  CombinatorialContracts.instDecidableEqQueryKind)
                CombinatorialContracts.QueryKind.cost
                (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                  (List.{0} CombinatorialContracts.QueryKind) executed))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) :=
  @CombinatorialContracts.Paper.theorem1_empty

/-- T2, S16: `CombinatorialContracts.Paper.theorem2`. -/
theorem claim_003.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) {oracle : Real → Finset.{u_1} ι}
  (ho : @CombinatorialContracts.IsExactPositiveOracle.{u_1} ι inst inst_1 M oracle) {ε : Real}
  (hε : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
  (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hn :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Fintype.card.{u_1} ι inst)),
  have executed :
    Prod.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind) :=
    @CombinatorialContracts.OracleProgram.eval.{u_1, u_1} ι (CombinatorialContracts.OracleRun.{u_1} ι) oracle
      (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.Model.cost.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.OracleProgram.algorithm1Program.{u_1} ι inst inst_1 ε);
  have r : CombinatorialContracts.QueryRecord.{u_1} ι :=
    @CombinatorialContracts.OracleRun.output.{u_1} ι
      (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
        executed);
  And
    (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@CombinatorialContracts.QueryRecord.share.{u_1} ι r))
    (And
      (@CombinatorialContracts.IsResponse.{u_1} ι inst inst_1 M (@CombinatorialContracts.QueryRecord.share.{u_1} ι r)
        (@CombinatorialContracts.QueryRecord.response.{u_1} ι r))
      (And
        (@Eq.{1} Real (@CombinatorialContracts.QueryRecord.reward.{u_1} ι r)
          (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
            (@CombinatorialContracts.QueryRecord.response.{u_1} ι r)))
        (And
          (@Eq.{1} Real (@CombinatorialContracts.QueryRecord.utility.{u_1} ι r)
            (@CombinatorialContracts.principal.{u_1} ι inst inst_1 M
              (@CombinatorialContracts.QueryRecord.share.{u_1} ι r)))
          (And
            (@LE.le.{0} Real Real.instLE
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
                (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M))
              (@CombinatorialContracts.principal.{u_1} ι inst inst_1 M
                (@CombinatorialContracts.QueryRecord.share.{u_1} ι r)))
            (And
              (@Membership.mem.{u_1, u_1} (CombinatorialContracts.QueryRecord.{u_1} ι)
                (List.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι))
                (@List.instMembership.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι))
                (@List.cons.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι)
                  (@CombinatorialContracts.OracleRun.initial.{u_1} ι
                    (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed))
                  (@CombinatorialContracts.OracleRun.grid.{u_1} ι
                    (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed)))
                r)
              (And
                (@Eq.{1} Nat
                  (@List.count.{0} CombinatorialContracts.QueryKind
                    (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                      CombinatorialContracts.instDecidableEqQueryKind)
                    CombinatorialContracts.QueryKind.response
                    (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed))
                  (@CombinatorialContracts.OracleRun.responseQueries.{u_1} ι
                    (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed)))
                (And
                  (@Eq.{1} Nat
                    (@List.count.{0} CombinatorialContracts.QueryKind
                      (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                        CombinatorialContracts.instDecidableEqQueryKind)
                      CombinatorialContracts.QueryKind.reward
                      (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                        (List.{0} CombinatorialContracts.QueryKind) executed))
                    (@CombinatorialContracts.OracleRun.rewardQueries.{u_1} ι inst
                      (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                        (List.{0} CombinatorialContracts.QueryKind) executed)))
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@List.count.{0} CombinatorialContracts.QueryKind
                          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                            CombinatorialContracts.instDecidableEqQueryKind)
                          CombinatorialContracts.QueryKind.response
                          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                            (List.{0} CombinatorialContracts.QueryKind) executed)))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 20)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
                            (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst)))
                          (Real.log
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                        ε))
                    (And
                      (@LE.le.{0} Real Real.instLE
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@List.count.{0} CombinatorialContracts.QueryKind
                            (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                              CombinatorialContracts.instDecidableEqQueryKind)
                            CombinatorialContracts.QueryKind.reward
                            (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                              (List.{0} CombinatorialContracts.QueryKind) executed)))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 20)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
                              (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst)))
                            (Real.log
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                          ε))
                      (@Eq.{1} Nat
                        (@List.count.{0} CombinatorialContracts.QueryKind
                          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                            CombinatorialContracts.instDecidableEqQueryKind)
                          CombinatorialContracts.QueryKind.cost
                          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                            (List.{0} CombinatorialContracts.QueryKind) executed))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))) :=
  @CombinatorialContracts.Paper.theorem2

/-- T2: `CombinatorialContracts.Paper.theorem2_empty`. -/
theorem claim_004.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) {oracle : Real → Finset.{u_1} ι}
  (ho : @CombinatorialContracts.IsExactPositiveOracle.{u_1} ι inst inst_1 M oracle)
  (hn : @Eq.{1} Nat (@Fintype.card.{u_1} ι inst) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (ε : Real),
  have executed :
    Prod.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind) :=
    @CombinatorialContracts.OracleProgram.eval.{u_1, u_1} ι (CombinatorialContracts.OracleRun.{u_1} ι) oracle
      (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.Model.cost.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.OracleProgram.algorithm1Program.{u_1} ι inst inst_1 ε);
  And
    (@Eq.{1} Real
      (@CombinatorialContracts.QueryRecord.share.{u_1} ι
        (@CombinatorialContracts.OracleRun.output.{u_1} ι
          (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed)))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (And
      (@Eq.{1} Real
        (@CombinatorialContracts.principal.{u_1} ι inst inst_1 M
          (@CombinatorialContracts.QueryRecord.share.{u_1} ι
            (@CombinatorialContracts.OracleRun.output.{u_1} ι
              (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
                executed))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (And
        (@Eq.{1} Real (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (And
          (@Eq.{1} Nat
            (@List.count.{0} CombinatorialContracts.QueryKind
              (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                CombinatorialContracts.instDecidableEqQueryKind)
              CombinatorialContracts.QueryKind.response
              (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
                executed))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (And
            (@Eq.{1} Nat
              (@List.count.{0} CombinatorialContracts.QueryKind
                (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                  CombinatorialContracts.instDecidableEqQueryKind)
                CombinatorialContracts.QueryKind.reward
                (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                  (List.{0} CombinatorialContracts.QueryKind) executed))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq.{1} Nat
              (@List.count.{0} CombinatorialContracts.QueryKind
                (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                  CombinatorialContracts.instDecidableEqQueryKind)
                CombinatorialContracts.QueryKind.cost
                (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                  (List.{0} CombinatorialContracts.QueryKind) executed))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) :=
  @CombinatorialContracts.Paper.theorem2_empty

/-- C3: `CombinatorialContracts.LowerBounds.corollary3_exact_worst_instance`. -/
theorem claim_005.{u_1} :
  (∀ {Ω : Type u_1} [inst : MeasurableSpace.{u_1} Ω] (μ : @MeasureTheory.Measure.{u_1} Ω inst)
  [@MeasureTheory.IsProbabilityMeasure.{u_1} Ω inst μ]
  (program : (n : Nat) → Ω → CombinatorialContracts.SupplyProgram.{0, 0} (Fin n) Real) (δ C : Real) (d : Nat)
  (hδ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ)
  (hs :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
        ∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
              (CombinatorialContracts.LowerBounds.hiddenIndices n) k →
            @MeasureTheory.Integrable.{0, u_1} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@SeminormedAddGroup.toContinuousENorm.{0} Real
                (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))))
              Ω inst (fun (ω : Ω) => CombinatorialContracts.LowerBounds.exactIndicator n (program n ω) k) μ)
  (hgood :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
        ∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
              (CombinatorialContracts.LowerBounds.hiddenIndices n) k →
            @LE.le.{0} Real Real.instLE δ
              (@MeasureTheory.integral.{u_1, 0} Ω Real Real.normedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                inst μ fun (ω : Ω) => CombinatorialContracts.LowerBounds.exactIndicator n (program n ω) k))
  (hQ :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
        ∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
              (CombinatorialContracts.LowerBounds.hiddenIndices n) k →
            @Measurable.{u_1, 0} Ω Real inst Real.measurableSpace fun (ω : Ω) =>
              @Nat.cast.{0} Real Real.instNatCast
                (@List.count.{0} CombinatorialContracts.QueryKind
                  (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                    CombinatorialContracts.instDecidableEqQueryKind)
                  CombinatorialContracts.QueryKind.response
                  (@Prod.snd.{0, 0} Real (List.{0} CombinatorialContracts.QueryKind)
                    (@CombinatorialContracts.LowerBounds.execute.{0} Real n k (program n ω)))))
  (hV :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
        @Measurable.{u_1, 0} Ω Real inst Real.measurableSpace fun (ω : Ω) =>
          CombinatorialContracts.LowerBounds.expectedValueCalls n (program n ω))
  (hpoly :
    @Filter.Eventually.{0} Nat
      (fun (n : Nat) =>
        @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
          (@MeasureTheory.lintegral.{u_1} Ω inst μ fun (ω : Ω) =>
            ENNReal.ofReal (CombinatorialContracts.LowerBounds.expectedValueCalls n (program n ω)))
          (ENNReal.ofReal
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast n)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                d))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)),
  @Filter.Eventually.{0} Nat
    (fun (n : Nat) =>
      @Exists.{1} Nat fun (k : Nat) =>
        And
          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
            (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
          (@LE.le.{0} ENNReal
            (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
            (ENNReal.ofReal
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                n))
            (@MeasureTheory.lintegral.{u_1} Ω inst μ fun (ω : Ω) =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
                (@List.count.{0} CombinatorialContracts.QueryKind
                  (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                    CombinatorialContracts.instDecidableEqQueryKind)
                  CombinatorialContracts.QueryKind.response
                  (@Prod.snd.{0, 0} Real (List.{0} CombinatorialContracts.QueryKind)
                    (@CombinatorialContracts.LowerBounds.execute.{0} Real n k (program n ω)))))))
    (@Filter.atTop.{0} Nat Nat.instPreorder)) :=
  @CombinatorialContracts.LowerBounds.corollary3_exact_worst_instance

/-- L4: `CombinatorialContracts.response_reward_monotone`. -/
theorem claim_006.{u} :
  (∀ {ι : Type u} [inst : Fintype.{u} ι] [inst_1 : DecidableEq.{u + 1} ι]
  (M : @CombinatorialContracts.Model.{u} ι inst inst_1) {α β : Real} {S T : Finset.{u} ι}
  (hαβ : @LE.le.{0} Real Real.instLE α β) (hS : @CombinatorialContracts.IsResponse.{u} ι inst inst_1 M α S)
  (hT : @CombinatorialContracts.IsResponse.{u} ι inst inst_1 M β T),
  @LE.le.{0} Real Real.instLE (@CombinatorialContracts.Model.reward.{u} ι inst inst_1 M S)
    (@CombinatorialContracts.Model.reward.{u} ι inst inst_1 M T)) :=
  @CombinatorialContracts.response_reward_monotone

/-- L4: `CombinatorialContracts.response_reward_mono`. -/
theorem claim_007.{u} :
  (∀ {ι : Type u} [inst : Fintype.{u} ι] [inst_1 : DecidableEq.{u + 1} ι]
  (M : @CombinatorialContracts.Model.{u} ι inst inst_1),
  @Monotone.{0, 0} Real Real Real.instPreorder Real.instPreorder fun (α : Real) =>
    @CombinatorialContracts.Model.reward.{u} ι inst inst_1 M (@CombinatorialContracts.response.{u} ι inst inst_1 M α)) :=
  @CombinatorialContracts.response_reward_mono

/-- L5: `CombinatorialContracts.welfare_profit_comparison`. -/
theorem claim_008.{u_1} :
  (∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (M : CombinatorialContracts.Model ι),
  CombinatorialContracts.optimalValue M ≤ CombinatorialContracts.welfare M ∧
  CombinatorialContracts.welfare M ≤ (Fintype.card ι : ℝ) * CombinatorialContracts.optimalValue M) :=
  @CombinatorialContracts.welfare_profit_comparison

/-- L6: `CombinatorialContracts.reward_anchored_scale_of_optimal_response`. -/
theorem claim_009.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) {α : Real} {S : Finset.{u_1} ι}
  (hα :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      α)
  (hS : @CombinatorialContracts.IsResponse.{u_1} ι inst inst_1 M α S)
  (hoptimal :
    @Eq.{1} Real
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α)
        (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M S))
      (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M))
  (hopt :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M))
  {j : ι} (hj : @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instMembership.{u_1} ι) S j)
  (hmax :
    ∀ (i : ι),
      @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instMembership.{u_1} ι) S i →
        @LE.le.{0} Real Real.instLE
          (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
            (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) i))
          (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
            (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j))),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
        (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j)))
    (And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
              (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j)))))
      (And
        (@LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
                (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α))
        (And
          (@LE.le.{0} Real Real.instLE
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α)
            (@Min.min.{0} Real Real.instMin (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M)
                (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
                  (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j)))))
          (@LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Min.min.{0} Real Real.instMin (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M)
                  (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
                    (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
                    (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j)))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))) :=
  @CombinatorialContracts.reward_anchored_scale_of_optimal_response

/-- T7: `CombinatorialContracts.Paper.theorem7`. -/
theorem claim_010.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) {oracle : Nat → Real → Finset.{u_1} ι} {ε τ : Real}
  (ho : @CombinatorialContracts.IsApproxOracle.{u_1} ι inst inst_1 M τ oracle)
  (hε : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
  (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hτ : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) τ)
  (hn :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Fintype.card.{u_1} ι inst)),
  have executed :
    Prod.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind) :=
    @CombinatorialContracts.OracleProgram.evalIndexed.{u_1, u_1} ι (CombinatorialContracts.OracleRun.{u_1} ι) oracle
      (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.Model.cost.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.OracleProgram.robustProgram.{u_1} ι inst inst_1 ε τ)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
  have r : CombinatorialContracts.QueryRecord.{u_1} ι :=
    @CombinatorialContracts.OracleRun.output.{u_1} ι
      (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
        executed);
  And
    (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@CombinatorialContracts.QueryRecord.share.{u_1} ι r))
    (And
      (@CombinatorialContracts.IsApproxBestResponse.{u_1} ι inst inst_1 M τ
        (@CombinatorialContracts.QueryRecord.share.{u_1} ι r) (@CombinatorialContracts.QueryRecord.response.{u_1} ι r))
      (And
        (@Eq.{1} Real (@CombinatorialContracts.QueryRecord.reward.{u_1} ι r)
          (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
            (@CombinatorialContracts.QueryRecord.response.{u_1} ι r)))
        (And
          (@LE.le.{0} Real Real.instLE
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
                (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  τ)
                ε))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@CombinatorialContracts.QueryRecord.share.{u_1} ι r))
              (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
                (@CombinatorialContracts.QueryRecord.response.{u_1} ι r))))
          (And
            (@Membership.mem.{u_1, u_1} (CombinatorialContracts.QueryRecord.{u_1} ι)
              (List.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι))
              (@List.instMembership.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι))
              (@List.cons.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι)
                (@CombinatorialContracts.OracleRun.initial.{u_1} ι
                  (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                    (List.{0} CombinatorialContracts.QueryKind) executed))
                (@CombinatorialContracts.OracleRun.grid.{u_1} ι
                  (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                    (List.{0} CombinatorialContracts.QueryKind) executed)))
              r)
            (And
              (@Exists.{1} Nat fun (t : Nat) =>
                @Eq.{u_1 + 1} (CombinatorialContracts.QueryRecord.{u_1} ι) r
                  (@CombinatorialContracts.QueryRecord.query.{u_1} ι (oracle t)
                    (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M)
                    (@CombinatorialContracts.QueryRecord.share.{u_1} ι r)))
              (And
                (@Eq.{1} Nat
                  (@List.count.{0} CombinatorialContracts.QueryKind
                    (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                      CombinatorialContracts.instDecidableEqQueryKind)
                    CombinatorialContracts.QueryKind.response
                    (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed))
                  (@CombinatorialContracts.OracleRun.responseQueries.{u_1} ι
                    (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                      (List.{0} CombinatorialContracts.QueryKind) executed)))
                (And
                  (@Eq.{1} Nat
                    (@List.count.{0} CombinatorialContracts.QueryKind
                      (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                        CombinatorialContracts.instDecidableEqQueryKind)
                      CombinatorialContracts.QueryKind.reward
                      (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                        (List.{0} CombinatorialContracts.QueryKind) executed))
                    (@CombinatorialContracts.OracleRun.rewardQueries.{u_1} ι inst
                      (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                        (List.{0} CombinatorialContracts.QueryKind) executed)))
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@List.count.{0} CombinatorialContracts.QueryKind
                          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                            CombinatorialContracts.instDecidableEqQueryKind)
                          CombinatorialContracts.QueryKind.response
                          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                            (List.{0} CombinatorialContracts.QueryKind) executed)))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 20)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
                            (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst)))
                          (Real.log
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                        ε))
                    (And
                      (@LE.le.{0} Real Real.instLE
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@List.count.{0} CombinatorialContracts.QueryKind
                            (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                              CombinatorialContracts.instDecidableEqQueryKind)
                            CombinatorialContracts.QueryKind.reward
                            (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                              (List.{0} CombinatorialContracts.QueryKind) executed)))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 20)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
                              (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst)))
                            (Real.log
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                          ε))
                      (@Eq.{1} Nat
                        (@List.count.{0} CombinatorialContracts.QueryKind
                          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                            CombinatorialContracts.instDecidableEqQueryKind)
                          CombinatorialContracts.QueryKind.cost
                          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                            (List.{0} CombinatorialContracts.QueryKind) executed))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))) :=
  @CombinatorialContracts.Paper.theorem7

/-- T7: `CombinatorialContracts.Paper.theorem7_empty`. -/
theorem claim_011.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) (oracle : Nat → Real → Finset.{u_1} ι)
  (hn : @Eq.{1} Nat (@Fintype.card.{u_1} ι inst) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (ε : Real) {τ : Real}
  (hτ : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) τ),
  have executed :
    Prod.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind) :=
    @CombinatorialContracts.OracleProgram.evalIndexed.{u_1, u_1} ι (CombinatorialContracts.OracleRun.{u_1} ι) oracle
      (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.Model.cost.{u_1} ι inst inst_1 M)
      (@CombinatorialContracts.OracleProgram.robustProgram.{u_1} ι inst inst_1 ε τ)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
  And
    (@Eq.{1} Real
      (@CombinatorialContracts.QueryRecord.share.{u_1} ι
        (@CombinatorialContracts.OracleRun.output.{u_1} ι
          (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed)))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (And
      (@Eq.{u_1 + 1} (Finset.{u_1} ι)
        (@CombinatorialContracts.QueryRecord.response.{u_1} ι
          (@CombinatorialContracts.OracleRun.output.{u_1} ι
            (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
              executed)))
        (@EmptyCollection.emptyCollection.{u_1} (Finset.{u_1} ι) (@Finset.instEmptyCollection.{u_1} ι)))
      (And
        (@Eq.{1} Real
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@CombinatorialContracts.QueryRecord.share.{u_1} ι
                (@CombinatorialContracts.OracleRun.output.{u_1} ι
                  (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                    (List.{0} CombinatorialContracts.QueryKind) executed))))
            (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
              (@CombinatorialContracts.QueryRecord.response.{u_1} ι
                (@CombinatorialContracts.OracleRun.output.{u_1} ι
                  (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                    (List.{0} CombinatorialContracts.QueryKind) executed)))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (And
          (@Eq.{1} Real (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M)
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (And
            (@Eq.{1} Nat
              (@List.count.{0} CombinatorialContracts.QueryKind
                (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                  CombinatorialContracts.instDecidableEqQueryKind)
                CombinatorialContracts.QueryKind.response
                (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                  (List.{0} CombinatorialContracts.QueryKind) executed))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (And
              (@Eq.{1} Nat
                (@List.count.{0} CombinatorialContracts.QueryKind
                  (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                    CombinatorialContracts.instDecidableEqQueryKind)
                  CombinatorialContracts.QueryKind.reward
                  (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                    (List.{0} CombinatorialContracts.QueryKind) executed))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq.{1} Nat
                (@List.count.{0} CombinatorialContracts.QueryKind
                  (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                    CombinatorialContracts.instDecidableEqQueryKind)
                  CombinatorialContracts.QueryKind.cost
                  (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι)
                    (List.{0} CombinatorialContracts.QueryKind) executed))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) :=
  @CombinatorialContracts.Paper.theorem7_empty

/-- T8, S23: `CombinatorialContracts.LowerBounds.hard_family`. -/
theorem claim_012 :
  (∀ {n : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
  (k : CombinatorialContracts.LowerBounds.Hidden n),
  And
    (@CombinatorialContracts.HasAdditiveReward.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
      (CombinatorialContracts.LowerBounds.model n
        (@Subtype.val.{1} Nat
          (fun (k : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
              (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
          k)
        (@And.left
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                  (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
              k))
          (And
            (@LT.lt.{0} Nat instLTNat
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                    (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                k)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
            (@LE.le.{0} Nat instLENat
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                      (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                  k))))
          (@CombinatorialContracts.LowerBounds.hidden_properties n hn k))))
    (And
      (@Monotone.{0, 0} (Finset.{0} (Fin n)) Real
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin n)) (@Finset.partialOrder.{0} (Fin n))) Real.instPreorder
        (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
          (CombinatorialContracts.LowerBounds.model n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                  (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
              k)
            (@And.left
              (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                      (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                  k))
              (And
                (@LT.lt.{0} Nat instLTNat
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                        (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                    k)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                (@LE.le.{0} Nat instLENat
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Subtype.val.{1} Nat
                      (fun (k : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                          (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                      k))))
              (@CombinatorialContracts.LowerBounds.hidden_properties n hn k)))))
      (And
        (∀ (S T : Finset.{0} (Fin n)),
          @HasSubset.Subset.{0} (Finset.{0} (Fin n)) (@Finset.instHasSubset.{0} (Fin n)) S T →
            ∀ (i : Fin n),
              Not (@Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n)) T i) →
                @LE.le.{0} Real Real.instLE
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                      (CombinatorialContracts.LowerBounds.model n
                        (@Subtype.val.{1} Nat
                          (fun (k : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                              (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                          k)
                        (@And.left
                          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                  (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                              k))
                          (And
                            (@LT.lt.{0} Nat instLTNat
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                    (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                                k)
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                            (@LE.le.{0} Nat instLENat
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                      (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                                  k))))
                          (@CombinatorialContracts.LowerBounds.hidden_properties n hn k)))
                      (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n))
                        (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) i S))
                    (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                      (CombinatorialContracts.LowerBounds.model n
                        (@Subtype.val.{1} Nat
                          (fun (k : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                              (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                          k)
                        (@And.left
                          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                  (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                              k))
                          (And
                            (@LT.lt.{0} Nat instLTNat
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                    (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                                k)
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                            (@LE.le.{0} Nat instLENat
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                      (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                                  k))))
                          (@CombinatorialContracts.LowerBounds.hidden_properties n hn k)))
                      S))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                      (CombinatorialContracts.LowerBounds.model n
                        (@Subtype.val.{1} Nat
                          (fun (k : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                              (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                          k)
                        (@And.left
                          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                  (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                              k))
                          (And
                            (@LT.lt.{0} Nat instLTNat
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                    (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                                k)
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                            (@LE.le.{0} Nat instLENat
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                      (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                                  k))))
                          (@CombinatorialContracts.LowerBounds.hidden_properties n hn k)))
                      (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n))
                        (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) i T))
                    (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                      (CombinatorialContracts.LowerBounds.model n
                        (@Subtype.val.{1} Nat
                          (fun (k : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                              (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                          k)
                        (@And.left
                          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                  (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                              k))
                          (And
                            (@LT.lt.{0} Nat instLTNat
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                    (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                                k)
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                            (@LE.le.{0} Nat instLENat
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                                      (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                                  k))))
                          (@CombinatorialContracts.LowerBounds.hidden_properties n hn k)))
                      T)))
        (@Eq.{1} Real
          (@CombinatorialContracts.optimalValue.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
            (CombinatorialContracts.LowerBounds.model n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                    (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                k)
              (@And.left
                (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                        (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                    k))
                (And
                  (@LT.lt.{0} Nat instLTNat
                    (@Subtype.val.{1} Nat
                      (fun (k : Nat) =>
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                          (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                      k)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                  (@LE.le.{0} Nat instLENat
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                            (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                        k))))
                (@CombinatorialContracts.LowerBounds.hidden_properties n hn k))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (CombinatorialContracts.LowerBounds.perturbation
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Nat.cast.{0} Real Real.instNatCast
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
                      (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
                  k)))))))) :=
  @CombinatorialContracts.LowerBounds.hard_family

/-- T8, S29: `CombinatorialContracts.LowerBounds.accuracy_binary_bounds`. -/
theorem claim_013 :
  (∀ {n : Nat} (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
  And
    (@LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 32)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            n)))
      (CombinatorialContracts.LowerBounds.accuracy
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@LE.le.{0} Real Real.instLE
      (CombinatorialContracts.LowerBounds.accuracy
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 16)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            n))))) :=
  @CombinatorialContracts.LowerBounds.accuracy_binary_bounds

/-- T8, S29, S34: `CombinatorialContracts.LowerBounds.theorem8_worst_instance`. -/
theorem claim_014.{u_1} :
  (∀ {Ω : Type u_1} [inst : MeasurableSpace.{u_1} Ω] (μ : @MeasureTheory.Measure.{u_1} Ω inst)
  [@MeasureTheory.IsProbabilityMeasure.{u_1} Ω inst μ]
  (program : (n : Nat) → Ω → CombinatorialContracts.SupplyProgram.{0, 0} (Fin n) Real) (δ C : Real) (d : Nat)
  (hδ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ)
  (hs :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
        ∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
              (CombinatorialContracts.LowerBounds.hiddenIndices n) k →
            @MeasureTheory.Integrable.{0, u_1} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@SeminormedAddGroup.toContinuousENorm.{0} Real
                (@SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))))
              Ω inst (fun (ω : Ω) => CombinatorialContracts.LowerBounds.approximationIndicator n (program n ω) k) μ)
  (hgood :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
        ∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
              (CombinatorialContracts.LowerBounds.hiddenIndices n) k →
            @LE.le.{0} Real Real.instLE δ
              (@MeasureTheory.integral.{u_1, 0} Ω Real Real.normedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                inst μ fun (ω : Ω) => CombinatorialContracts.LowerBounds.approximationIndicator n (program n ω) k))
  (hQ :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
        ∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
              (CombinatorialContracts.LowerBounds.hiddenIndices n) k →
            @Measurable.{u_1, 0} Ω Real inst Real.measurableSpace fun (ω : Ω) =>
              @Nat.cast.{0} Real Real.instNatCast
                (@List.count.{0} CombinatorialContracts.QueryKind
                  (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                    CombinatorialContracts.instDecidableEqQueryKind)
                  CombinatorialContracts.QueryKind.response
                  (@Prod.snd.{0, 0} Real (List.{0} CombinatorialContracts.QueryKind)
                    (@CombinatorialContracts.LowerBounds.execute.{0} Real n k (program n ω)))))
  (hV :
    ∀ (n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
        @Measurable.{u_1, 0} Ω Real inst Real.measurableSpace fun (ω : Ω) =>
          CombinatorialContracts.LowerBounds.expectedValueCalls n (program n ω))
  (hpoly :
    @Filter.Eventually.{0} Nat
      (fun (n : Nat) =>
        @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
          (@MeasureTheory.lintegral.{u_1} Ω inst μ fun (ω : Ω) =>
            ENNReal.ofReal (CombinatorialContracts.LowerBounds.expectedValueCalls n (program n ω)))
          (ENNReal.ofReal
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast n)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                d))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)),
  @Filter.Eventually.{0} Nat
    (fun (n : Nat) =>
      @Exists.{1} Nat fun (k : Nat) =>
        And
          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
            (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
          (@LE.le.{0} ENNReal
            (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
            (ENNReal.ofReal
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                n))
            (@MeasureTheory.lintegral.{u_1} Ω inst μ fun (ω : Ω) =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
                (@List.count.{0} CombinatorialContracts.QueryKind
                  (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                    CombinatorialContracts.instDecidableEqQueryKind)
                  CombinatorialContracts.QueryKind.response
                  (@Prod.snd.{0, 0} Real (List.{0} CombinatorialContracts.QueryKind)
                    (@CombinatorialContracts.LowerBounds.execute.{0} Real n k (program n ω)))))))
    (@Filter.atTop.{0} Nat Nat.instPreorder)) :=
  @CombinatorialContracts.LowerBounds.theorem8_worst_instance

/-- T8, S33: `CombinatorialContracts.LowerBounds.randomized_strategy_program_exact`. -/
theorem claim_015.{u_1, u_2} :
  (∀ {Ω : Type u_1} {α : Type u_2} (n : Nat)
  (strategy : Ω → CombinatorialContracts.LowerBounds.HistoryStrategy.{0, u_2} (Fin n) α) (fallback : α) (ω : Ω)
  (hterm :
    ∀ (k : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
          (CombinatorialContracts.LowerBounds.hiddenIndices n) k →
        @Exists.{u_2 + 1} (Prod.{u_2, 0} α (List.{0} CombinatorialContracts.QueryKind))
          fun (result : Prod.{u_2, 0} α (List.{0} CombinatorialContracts.QueryKind)) =>
          @CombinatorialContracts.LowerBounds.HiddenStrategyTerminatesWith.{u_2} α n k (strategy ω) result)
  {k : Nat}
  (hk :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
      (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
  {result : Prod.{u_2, 0} α (List.{0} CombinatorialContracts.QueryKind)}
  (hr : @CombinatorialContracts.LowerBounds.HiddenStrategyTerminatesWith.{u_2} α n k (strategy ω) result),
  @Eq.{u_2 + 1} (Prod.{u_2, 0} α (List.{0} CombinatorialContracts.QueryKind))
    (@CombinatorialContracts.LowerBounds.execute.{u_2} α n k
      (@CombinatorialContracts.LowerBounds.finiteStrategyProgram.{u_2} α n (strategy ω) fallback))
    result) :=
  @CombinatorialContracts.LowerBounds.randomized_strategy_program_exact

/-- P9i, S30: `CombinatorialContracts.Tightness.proposition9_i`. -/
theorem claim_016 :
  (∀ (m : Nat) (η : Real) (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
  (hη : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) η)
  (hη1 : @LT.lt.{0} Real Real.instLT η (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @Exists.{1}
    (@CombinatorialContracts.Model.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
      (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
      fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
      @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a b)
    fun
      (M :
        @CombinatorialContracts.Model.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
          (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
          fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
          @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a b) =>
    And
      (@CombinatorialContracts.HasAdditiveReward.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
        (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
        (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
          @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a b)
        M)
      (And
        (@Eq.{1} Real
          (@CombinatorialContracts.Model.reward.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
            (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
            (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
              @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a b)
            M
            (@Finset.univ.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
              (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (And
          (∀ (T : Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m)),
            @LE.le.{0} Real Real.instLE
              (@CombinatorialContracts.Model.reward.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
                (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                  @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a b)
                M T)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@Exists.{1} Real fun (α : Real) =>
            And
              (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                (@Set.Icc.{0} Real Real.instPreorder
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                α)
              (@Exists.{1} (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                fun (S : Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m)) =>
                And
                  (@CombinatorialContracts.IsResponse.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
                    (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                    (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                      @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a b)
                    M α S)
                  (And
                    (@Eq.{1} Real
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α)
                        (@CombinatorialContracts.Model.reward.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
                          (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                          (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                            @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a
                              b)
                          M S))
                      (@CombinatorialContracts.optimalValue.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
                        (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                        (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                          @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a b)
                        M))
                    (And
                      (∀ (β : Real),
                        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                            (@Set.Icc.{0} Real Real.instPreorder
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                            β →
                          ∀ (T : Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m)),
                            @CombinatorialContracts.IsResponse.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
                                (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                  @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                    (instDecidableEqFin m) a b)
                                M β T →
                              @Eq.{1} Real
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) β)
                                    (@CombinatorialContracts.Model.reward.{0}
                                      (CombinatorialContracts.Tightness.Bundle.Action m)
                                      (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                      (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                        @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                          (instDecidableEqFin m) a b)
                                      M T))
                                  (@CombinatorialContracts.optimalValue.{0}
                                    (CombinatorialContracts.Tightness.Bundle.Action m)
                                    (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                    (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                      @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                        (instDecidableEqFin m) a b)
                                    M) →
                                And (@Eq.{1} Real β α)
                                  (@Eq.{1} (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m)) T S))
                      (@Exists.{1} (CombinatorialContracts.Tightness.Bundle.Action m)
                        fun (j : CombinatorialContracts.Tightness.Bundle.Action m) =>
                        And
                          (@Membership.mem.{0, 0} (CombinatorialContracts.Tightness.Bundle.Action m)
                            (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                            (@Finset.instMembership.{0} (CombinatorialContracts.Tightness.Bundle.Action m)) S j)
                          (And
                            (@LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@CombinatorialContracts.Model.reward.{0}
                                (CombinatorialContracts.Tightness.Bundle.Action m)
                                (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                  @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                    (instDecidableEqFin m) a b)
                                M
                                (@Singleton.singleton.{0, 0} (CombinatorialContracts.Tightness.Bundle.Action m)
                                  (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                  (@Finset.instSingleton.{0} (CombinatorialContracts.Tightness.Bundle.Action m)) j)))
                            (And
                              (∀ (i : CombinatorialContracts.Tightness.Bundle.Action m),
                                @Membership.mem.{0, 0} (CombinatorialContracts.Tightness.Bundle.Action m)
                                    (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                    (@Finset.instMembership.{0} (CombinatorialContracts.Tightness.Bundle.Action m)) S
                                    i →
                                  @LE.le.{0} Real Real.instLE
                                    (@CombinatorialContracts.Model.reward.{0}
                                      (CombinatorialContracts.Tightness.Bundle.Action m)
                                      (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                      (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                        @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                          (instDecidableEqFin m) a b)
                                      M
                                      (@Singleton.singleton.{0, 0} (CombinatorialContracts.Tightness.Bundle.Action m)
                                        (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                        (@Finset.instSingleton.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                        i))
                                    (@CombinatorialContracts.Model.reward.{0}
                                      (CombinatorialContracts.Tightness.Bundle.Action m)
                                      (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                      (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                        @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                          (instDecidableEqFin m) a b)
                                      M
                                      (@Singleton.singleton.{0, 0} (CombinatorialContracts.Tightness.Bundle.Action m)
                                        (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                        (@Finset.instSingleton.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                        j)))
                              (And
                                (@Eq.{1} Real
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@CombinatorialContracts.welfare.{0}
                                      (CombinatorialContracts.Tightness.Bundle.Action m)
                                      (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                      (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                        @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                          (instDecidableEqFin m) a b)
                                      M)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α)
                                      (@CombinatorialContracts.Model.reward.{0}
                                        (CombinatorialContracts.Tightness.Bundle.Action m)
                                        (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                        (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                          @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                            (instDecidableEqFin m) a b)
                                        M
                                        (@Singleton.singleton.{0, 0} (CombinatorialContracts.Tightness.Bundle.Action m)
                                          (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                          (@Finset.instSingleton.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                          j))))
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@Nat.cast.{0} Real Real.instNatCast m)
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) η)
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@Nat.cast.{0} Real Real.instNatCast m)
                                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                              (@Nat.instAtLeastTwoHAddOfNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                (@Nat.instNeZeroSucc
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) η)))
                                (@LE.le.{0} Real Real.instLE
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                      (@Nat.cast.{0} Real Real.instNatCast
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@OfNat.ofNat.{0} Real (nat_lit 16)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@CombinatorialContracts.welfare.{0}
                                      (CombinatorialContracts.Tightness.Bundle.Action m)
                                      (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                      (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                        @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                          (instDecidableEqFin m) a b)
                                      M)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) α)
                                      (@CombinatorialContracts.Model.reward.{0}
                                        (CombinatorialContracts.Tightness.Bundle.Action m)
                                        (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
                                        (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
                                          @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m)
                                            (instDecidableEqFin m) a b)
                                        M
                                        (@Singleton.singleton.{0, 0} (CombinatorialContracts.Tightness.Bundle.Action m)
                                          (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                          (@Finset.instSingleton.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
                                          j)))))))))))))))) :=
  @CombinatorialContracts.Tightness.proposition9_i

/-- P9ii, S30: `CombinatorialContracts.Tightness.proposition9_ii`. -/
theorem claim_017 :
  (∀ (n : Nat) (r : Real) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
  (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r),
  @Exists.{1} (@CombinatorialContracts.Model.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n))
    fun (M : @CombinatorialContracts.Model.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)) =>
    And (@CombinatorialContracts.HasAdditiveReward.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M)
      (And
        (@Eq.{1} Real
          (@CombinatorialContracts.Model.reward.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M
            (@Finset.univ.{0} (Fin n) (Fin.fintype n)))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (And
          (∀ (S : Finset.{0} (Fin n)),
            @LE.le.{0} Real Real.instLE
              (@CombinatorialContracts.Model.reward.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M S)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (And
            (@Monotone.{0, 0} (Finset.{0} (Fin n)) Real
              (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin n)) (@Finset.partialOrder.{0} (Fin n))) Real.instPreorder
              (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M))
            (And
              (∀ (S T : Finset.{0} (Fin n)),
                @HasSubset.Subset.{0} (Finset.{0} (Fin n)) (@Finset.instHasSubset.{0} (Fin n)) S T →
                  ∀ (i : Fin n),
                    Not (@Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n)) T i) →
                      @LE.le.{0} Real Real.instLE
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M
                            (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n))
                              (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) i S))
                          (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M S))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M
                            (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n))
                              (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) i T))
                          (@CombinatorialContracts.Model.cost.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M T)))
              (@Eq.{1} Real
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@CombinatorialContracts.welfare.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M)
                  (@CombinatorialContracts.optimalValue.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) M))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Nat.cast.{0} Real Real.instNatCast n)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@Nat.cast.{0} Real Real.instNatCast n)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    r)))))))) :=
  @CombinatorialContracts.Tightness.proposition9_ii

/-- P10: `CombinatorialContracts.EqualRevenue.proposition10`. -/
theorem claim_018 :
  (∀ {n : Nat} (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
  And
    (@Eq.{1} Real
      (@CombinatorialContracts.optimalValue.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
        (CombinatorialContracts.EqualRevenue.model n))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (And
      (@Eq.{1} Real
        (@CombinatorialContracts.welfare.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
          (CombinatorialContracts.EqualRevenue.model n))
        (CombinatorialContracts.EqualRevenue.harmonic
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (And
        (@LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast n)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (CombinatorialContracts.EqualRevenue.harmonic
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (And
          (@LE.le.{0} Real Real.instLE
            (CombinatorialContracts.EqualRevenue.harmonic
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Nat.cast.{0} Real Real.instNatCast n))
          (∀ (S : Finset.{0} (Fin n)) (j : Fin n),
            @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n)) S j →
              (∀ (i : Fin n),
                  @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instMembership.{0} (Fin n)) S i →
                    @LE.le.{0} Real Real.instLE
                      (@CombinatorialContracts.Model.reward.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                        (CombinatorialContracts.EqualRevenue.model n)
                        (@Singleton.singleton.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instSingleton.{0} (Fin n))
                          i))
                      (@CombinatorialContracts.Model.reward.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                        (CombinatorialContracts.EqualRevenue.model n)
                        (@Singleton.singleton.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instSingleton.{0} (Fin n))
                          j))) →
                And
                  (@LT.lt.{0} Real Real.instLT
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        (@CombinatorialContracts.Model.reward.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                          (CombinatorialContracts.EqualRevenue.model n)
                          (@Singleton.singleton.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instSingleton.{0} (Fin n))
                            j))))
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (CombinatorialContracts.EqualRevenue.critical
                        (@CombinatorialContracts.EqualRevenue.binaryIndex n S))))
                  (@LE.le.{0} Real Real.instLE
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (CombinatorialContracts.EqualRevenue.critical
                        (@CombinatorialContracts.EqualRevenue.binaryIndex n S)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@CombinatorialContracts.Model.reward.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                        (CombinatorialContracts.EqualRevenue.model n)
                        (@Singleton.singleton.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instSingleton.{0} (Fin n))
                          j))))))))) :=
  @CombinatorialContracts.EqualRevenue.proposition10

/-- S01: `CombinatorialContracts.exists_response`. -/
theorem claim_019.{u} :
  (∀ {ι : Type u} [inst : Fintype.{u} ι] [inst_1 : DecidableEq.{u + 1} ι]
  (M : @CombinatorialContracts.Model.{u} ι inst inst_1) (α : Real),
  @Exists.{u + 1} (Finset.{u} ι) fun (S : Finset.{u} ι) => @CombinatorialContracts.IsResponse.{u} ι inst inst_1 M α S) :=
  @CombinatorialContracts.exists_response

/-- S02: `CombinatorialContracts.exists_optimum`. -/
theorem claim_020.{u} :
  (∀ {ι : Type u} [inst : Fintype.{u} ι] [inst_1 : DecidableEq.{u + 1} ι]
  (M : @CombinatorialContracts.Model.{u} ι inst inst_1),
  @Exists.{1} Real fun (α : Real) =>
    And
      (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        α)
      (∀ (β : Real),
        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
            (@Set.Icc.{0} Real Real.instPreorder
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            β →
          @LE.le.{0} Real Real.instLE (@CombinatorialContracts.principal.{u} ι inst inst_1 M β)
            (@CombinatorialContracts.principal.{u} ι inst inst_1 M α))) :=
  @CombinatorialContracts.exists_optimum

/-- S03: `CombinatorialContracts.empty_ground_zero`. -/
theorem claim_021.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1)
  (hn : @Eq.{1} Nat (@Fintype.card.{u_1} ι inst) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  And
    (@Eq.{1} Real (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (@Eq.{1} Real (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) :=
  @CombinatorialContracts.empty_ground_zero

/-- S03: `CombinatorialContracts.EndpointRegression.empty_ground_optimalValue`. -/
theorem claim_022 :
  (∀
  (M :
    @CombinatorialContracts.Model.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))),
  @Eq.{1} Real
    (@CombinatorialContracts.optimalValue.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) M)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) :=
  @CombinatorialContracts.EndpointRegression.empty_ground_optimalValue

/-- S04: `CombinatorialContracts.principal_nonneg`. -/
theorem claim_023.{u} :
  (∀ {ι : Type u} [inst : Fintype.{u} ι] [inst_1 : DecidableEq.{u + 1} ι]
  (M : @CombinatorialContracts.Model.{u} ι inst inst_1) {α : Real}
  (hα : @LE.le.{0} Real Real.instLE α (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@CombinatorialContracts.principal.{u} ι inst inst_1 M α)) :=
  @CombinatorialContracts.principal_nonneg

/-- S04: `CombinatorialContracts.principal_le_welfare`. -/
theorem claim_024.{u} :
  (∀ {ι : Type u} [inst : Fintype.{u} ι] [inst_1 : DecidableEq.{u + 1} ι]
  (M : @CombinatorialContracts.Model.{u} ι inst inst_1) (α : Real),
  @LE.le.{0} Real Real.instLE (@CombinatorialContracts.principal.{u} ι inst inst_1 M α)
    (@CombinatorialContracts.welfare.{u} ι inst inst_1 M)) :=
  @CombinatorialContracts.principal_le_welfare

/-- S05: `CombinatorialContracts.welfare_eq_zero_iff_optimalValue_eq_zero`. -/
theorem claim_025.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1),
  Iff
    (@Eq.{1} Real (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (@Eq.{1} Real (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) :=
  @CombinatorialContracts.welfare_eq_zero_iff_optimalValue_eq_zero

/-- S06, S07: `CombinatorialContracts.FiniteEnvelope.exists_partition`. -/
theorem claim_026.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : Nonempty.{u_1 + 1} ι] (r c : ι → Real),
  @Exists.{1} Nat fun (k : Nat) =>
    @Exists.{1} (Nat → Real) fun (a : Nat → Real) =>
      @Exists.{u_1 + 1} (Nat → ι) fun (s : Nat → ι) =>
        And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
          (And
            (@Eq.{1} Real (a (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (And (@Eq.{1} Real (a k) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (And
                (∀ (t : Nat),
                  @LT.lt.{0} Nat instLTNat t k →
                    @LT.lt.{0} Real Real.instLT (a t)
                      (a
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (And
                  (∀ (t : Nat),
                    @LE.le.{0} Nat instLENat t k →
                      And
                        (@LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (a t))
                        (@LE.le.{0} Real Real.instLE (a t)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                  (And
                    (∀ (t : Nat),
                      @LT.lt.{0} Nat instLTNat t k →
                        ∀ (x : Real),
                          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                              (@Set.Icc.{0} Real Real.instPreorder (a t)
                                (a
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              x →
                            @CombinatorialContracts.FiniteEnvelope.IsActive.{u_1} ι r c x (s t))
                    (@Eq.{1} Real
                      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range k) fun (t : Nat) =>
                        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (a
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (a t))
                          (r (s t)))
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@CombinatorialContracts.FiniteEnvelope.envelope.{u_1} ι inst inst_1 r c
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (@CombinatorialContracts.FiniteEnvelope.envelope.{u_1} ι inst inst_1 r c
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))))))) :=
  @CombinatorialContracts.FiniteEnvelope.exists_partition

/-- S06: `CombinatorialContracts.FiniteEnvelope.exists_partition_max_slope`. -/
theorem claim_027.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : Nonempty.{u_1 + 1} ι] (r c : ι → Real),
  @Exists.{1} Nat fun (k : Nat) =>
    @Exists.{1} (Nat → Real) fun (a : Nat → Real) =>
      @Exists.{u_1 + 1} (Nat → ι) fun (s : Nat → ι) =>
        And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
          (And
            (@Eq.{1} Real (a (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (And (@Eq.{1} Real (a k) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (And
                (∀ (t : Nat),
                  @LT.lt.{0} Nat instLTNat t k →
                    @LT.lt.{0} Real Real.instLT (a t)
                      (a
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (And
                  (∀ (t : Nat),
                    @LE.le.{0} Nat instLENat t k →
                      And
                        (@LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (a t))
                        (@LE.le.{0} Real Real.instLE (a t)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                  (And
                    (∀ (t : Nat),
                      @LT.lt.{0} Nat instLTNat t k →
                        ∀ (x : Real),
                          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                              (@Set.Icc.{0} Real Real.instPreorder (a t)
                                (a
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              x →
                            @CombinatorialContracts.FiniteEnvelope.IsActive.{u_1} ι r c x (s t))
                    (And
                      (∀ (t : Nat),
                        @LT.lt.{0} Nat instLTNat t k →
                          ∀ (x : Real),
                            @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                                (@Set.Ico.{0} Real Real.instPreorder (a t)
                                  (a
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                x →
                              ∀ (j : ι),
                                @CombinatorialContracts.FiniteEnvelope.IsActive.{u_1} ι r c x j →
                                  @LE.le.{0} Real Real.instLE (r j) (r (s t)))
                      (@Eq.{1} Real
                        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range k) fun (t : Nat) =>
                          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (a
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (a t))
                            (r (s t)))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@CombinatorialContracts.FiniteEnvelope.envelope.{u_1} ι inst inst_1 r c
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                          (@CombinatorialContracts.FiniteEnvelope.envelope.{u_1} ι inst inst_1 r c
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))))))))) :=
  @CombinatorialContracts.FiniteEnvelope.exists_partition_max_slope

/-- S08, S09: `CombinatorialContracts.finite_first_appearance_bound`. -/
theorem claim_028.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι] (f : Finset.{u_1} ι → Real)
  (hzero :
    @Eq.{1} Real (f (@EmptyCollection.emptyCollection.{u_1} (Finset.{u_1} ι) (@Finset.instEmptyCollection.{u_1} ι)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hnonneg :
    ∀ (S : Finset.{u_1} ι),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (f S))
  (hmono :
    @Monotone.{u_1, 0} (Finset.{u_1} ι) Real
      (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} ι) (@Finset.partialOrder.{u_1} ι)) Real.instPreorder f)
  (hsub :
    ∀ (S T : Finset.{u_1} ι),
      @LE.le.{0} Real Real.instLE (f (@Union.union.{u_1} (Finset.{u_1} ι) (@Finset.instUnion.{u_1} ι inst_1) S T))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (f S) (f T)))
  (k : Nat) (a : Nat → Real) (S : Nat → Finset.{u_1} ι) (P : Real)
  (hP : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) P)
  (hend : @Eq.{1} Real (a k) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hstep :
    ∀ (t : Nat),
      @LT.lt.{0} Nat instLTNat t k →
        @LE.le.{0} Real Real.instLE (a t)
          (a
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hupper :
    ∀ (t : Nat),
      @LT.lt.{0} Nat instLTNat t k →
        @LE.le.{0} Real Real.instLE (a t) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hprofit :
    ∀ (t : Nat),
      @LT.lt.{0} Nat instLTNat t k →
        @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (a t))
            (f (S t)))
          P),
  @LE.le.{0} Real Real.instLE
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range k) fun (t : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (a
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (a t))
        (f (S t)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst)) P)) :=
  @CombinatorialContracts.finite_first_appearance_bound

/-- S10: `CombinatorialContracts.subadditive_le_sum_singletons`. -/
theorem claim_029.{u_1} :
  (∀ {ι : Type u_1} [inst : DecidableEq.{u_1 + 1} ι] (f : Finset.{u_1} ι → Real)
  (hempty :
    @Eq.{1} Real (f (@EmptyCollection.emptyCollection.{u_1} (Finset.{u_1} ι) (@Finset.instEmptyCollection.{u_1} ι)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hsub :
    ∀ (S T : Finset.{u_1} ι),
      @LE.le.{0} Real Real.instLE (f (@Union.union.{u_1} (Finset.{u_1} ι) (@Finset.instUnion.{u_1} ι inst) S T))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (f S) (f T)))
  (S : Finset.{u_1} ι),
  @LE.le.{0} Real Real.instLE (f S)
    (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid S fun (i : ι) =>
      f (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) i))) :=
  @CombinatorialContracts.subadditive_le_sum_singletons

/-- S11: `CombinatorialContracts.exists_reward_anchor`. -/
theorem claim_030.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) (S : Finset.{u_1} ι)
  (hS :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M S)),
  @Exists.{u_1 + 1} ι fun (j : ι) =>
    And (@Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instMembership.{u_1} ι) S j)
      (And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
            (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j)))
        (And
          (@LE.le.{0} Real Real.instLE
            (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
              (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j))
            (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M S))
          (And
            (@LE.le.{0} Real Real.instLE (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M S)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} ι inst))
                (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
                  (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j))))
            (∀ (i : ι),
              @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instMembership.{u_1} ι) S i →
                @LE.le.{0} Real Real.instLE
                  (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
                    (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) i))
                  (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M
                    (@Singleton.singleton.{u_1, u_1} ι (Finset.{u_1} ι) (@Finset.instSingleton.{u_1} ι) j))))))) :=
  @CombinatorialContracts.exists_reward_anchor

/-- S12: `CombinatorialContracts.leastGridSteps_spec`. -/
theorem claim_031 :
  (∀ {ε R : Real}
  (hε : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
  (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hR : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) R),
  @LE.le.{0} Real Real.instLE
    (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
      (CombinatorialContracts.leastGridSteps
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
        R))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) R)) :=
  @CombinatorialContracts.leastGridSteps_spec

/-- S12: `CombinatorialContracts.leastGridSteps_minimal`. -/
theorem claim_032 :
  (∀ {q R : Real}
  (he :
    @Exists.{1} Nat fun (k : Nat) =>
      @LE.le.{0} Real Real.instLE
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) q k)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) R))
  {j : Nat} (hj : @LT.lt.{0} Nat instLTNat j (CombinatorialContracts.leastGridSteps q R)),
  @LT.lt.{0} Real Real.instLT
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) R)
    (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) q j)) :=
  @CombinatorialContracts.leastGridSteps_minimal

/-- S13: `CombinatorialContracts.geometric_cover_of_width`. -/
theorem claim_033 :
  (∀ {ε R b δ : Real}
  (hε : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
  (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hR : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) R)
  (hb : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hlo :
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b
        R)
      δ)
  (hhi : @LE.le.{0} Real Real.instLE δ b),
  @Exists.{1} Nat fun (k : Nat) =>
    And
      (@LT.lt.{0} Nat instLTNat k
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (CombinatorialContracts.leastGridSteps
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
            R)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (And
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
            δ)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          δ))) :=
  @CombinatorialContracts.geometric_cover_of_width

/-- S14: `CombinatorialContracts.shifted_contract_valid`. -/
theorem claim_034 :
  (∀ {q b : Real} {k : Nat}
  (hq : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) q)
  (hq1 : @LT.lt.{0} Real Real.instLT q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hb : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hb1 : @LE.le.{0} Real Real.instLE b (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) q
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
    (@LE.le.{0} Real Real.instLE
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) q
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) :=
  @CombinatorialContracts.shifted_contract_valid

/-- S15: `CombinatorialContracts.supplyResponse_iff_response`. -/
theorem claim_035.{u} :
  (∀ {ι : Type u} [inst : Fintype.{u} ι] [inst_1 : DecidableEq.{u + 1} ι]
  (M : @CombinatorialContracts.Model.{u} ι inst inst_1)
  (hadd : @CombinatorialContracts.HasAdditiveReward.{u} ι inst inst_1 M) {α : Real} {S : Finset.{u} ι}
  (hα : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) α),
  Iff
    (@CombinatorialContracts.IsSupplyResponse.{u} ι inst inst_1 M
      (fun (i : ι) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) α
          (@CombinatorialContracts.Model.reward.{u} ι inst inst_1 M
            (@Singleton.singleton.{u, u} ι (Finset.{u} ι) (@Finset.instSingleton.{u} ι) i)))
      S)
    (@CombinatorialContracts.IsResponse.{u} ι inst inst_1 M α S)) :=
  @CombinatorialContracts.supplyResponse_iff_response

/-- S16: `CombinatorialContracts.OracleRun.output_mem`. -/
theorem claim_036.{u_1} :
  (∀ {ι : Type u_1} (run : CombinatorialContracts.OracleRun.{u_1} ι),
  @Membership.mem.{u_1, u_1} (CombinatorialContracts.QueryRecord.{u_1} ι)
    (List.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι))
    (@List.instMembership.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι))
    (@List.cons.{u_1} (CombinatorialContracts.QueryRecord.{u_1} ι)
      (@CombinatorialContracts.OracleRun.initial.{u_1} ι run) (@CombinatorialContracts.OracleRun.grid.{u_1} ι run))
    (@CombinatorialContracts.OracleRun.output.{u_1} ι run)) :=
  @CombinatorialContracts.OracleRun.output_mem

/-- S17: `CombinatorialContracts.OracleProgram.algorithm1Program_counts`. -/
theorem claim_037.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι] (oracle : Real → Finset.{u_1} ι)
  (value costValue : Finset.{u_1} ι → Real) (ε : Real),
  have executed :
    Prod.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind) :=
    @CombinatorialContracts.OracleProgram.eval.{u_1, u_1} ι (CombinatorialContracts.OracleRun.{u_1} ι) oracle value
      costValue (@CombinatorialContracts.OracleProgram.algorithm1Program.{u_1} ι inst inst_1 ε);
  And
    (@Eq.{1} Nat
      (@List.count.{0} CombinatorialContracts.QueryKind
        (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
        CombinatorialContracts.QueryKind.response
        (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
          executed))
      (@CombinatorialContracts.OracleRun.responseQueries.{u_1} ι
        (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
          executed)))
    (And
      (@Eq.{1} Nat
        (@List.count.{0} CombinatorialContracts.QueryKind
          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
          CombinatorialContracts.QueryKind.reward
          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed))
        (@CombinatorialContracts.OracleRun.rewardQueries.{u_1} ι inst
          (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed)))
      (@Eq.{1} Nat
        (@List.count.{0} CombinatorialContracts.QueryKind
          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
          CombinatorialContracts.QueryKind.cost
          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed))
        (@CombinatorialContracts.OracleRun.costQueries.{u_1} ι
          (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed))))) :=
  @CombinatorialContracts.OracleProgram.algorithm1Program_counts

/-- S17: `CombinatorialContracts.SupplyProgram.algorithm_counts`. -/
theorem claim_038.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι] (supply : (ι → Real) → Finset.{u_1} ι)
  (value costValue : Finset.{u_1} ι → Real) (ε : Real),
  have executed :
    Prod.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind) :=
    @CombinatorialContracts.SupplyProgram.eval.{u_1, u_1} ι (CombinatorialContracts.OracleRun.{u_1} ι) supply value
      costValue (@CombinatorialContracts.SupplyProgram.algorithm.{u_1} ι inst inst_1 ε);
  And
    (@Eq.{1} Nat
      (@List.count.{0} CombinatorialContracts.QueryKind
        (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
        CombinatorialContracts.QueryKind.response
        (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
          executed))
      (@CombinatorialContracts.OracleRun.responseQueries.{u_1} ι
        (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
          executed)))
    (And
      (@Eq.{1} Nat
        (@List.count.{0} CombinatorialContracts.QueryKind
          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
          CombinatorialContracts.QueryKind.reward
          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed))
        (@Fintype.card.{u_1} ι inst))
      (@Eq.{1} Nat
        (@List.count.{0} CombinatorialContracts.QueryKind
          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
          CombinatorialContracts.QueryKind.cost
          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) :=
  @CombinatorialContracts.SupplyProgram.algorithm_counts

/-- S17: `CombinatorialContracts.OracleProgram.robustProgram_counts`. -/
theorem claim_039.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι] (oracle : Nat → Real → Finset.{u_1} ι)
  (value costValue : Finset.{u_1} ι → Real) (ε τ : Real),
  have executed :
    Prod.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind) :=
    @CombinatorialContracts.OracleProgram.evalIndexed.{u_1, u_1} ι (CombinatorialContracts.OracleRun.{u_1} ι) oracle
      value costValue (@CombinatorialContracts.OracleProgram.robustProgram.{u_1} ι inst inst_1 ε τ)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
  And
    (@Eq.{1} Nat
      (@List.count.{0} CombinatorialContracts.QueryKind
        (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
        CombinatorialContracts.QueryKind.response
        (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
          executed))
      (@CombinatorialContracts.OracleRun.responseQueries.{u_1} ι
        (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
          executed)))
    (And
      (@Eq.{1} Nat
        (@List.count.{0} CombinatorialContracts.QueryKind
          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
          CombinatorialContracts.QueryKind.reward
          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed))
        (@CombinatorialContracts.OracleRun.rewardQueries.{u_1} ι inst
          (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed)))
      (@Eq.{1} Nat
        (@List.count.{0} CombinatorialContracts.QueryKind
          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
          CombinatorialContracts.QueryKind.cost
          (@Prod.snd.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed))
        (@CombinatorialContracts.OracleRun.costQueries.{u_1} ι
          (@Prod.fst.{u_1, 0} (CombinatorialContracts.OracleRun.{u_1} ι) (List.{0} CombinatorialContracts.QueryKind)
            executed))))) :=
  @CombinatorialContracts.OracleProgram.robustProgram_counts

/-- S18: `CombinatorialContracts.leastGridSteps_add_one_bound`. -/
theorem claim_040 :
  (∀ {ε R : Real}
  (hε : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
  (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hR : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) R),
  @LE.le.{0} Real Real.instLE
    (@Nat.cast.{0} Real Real.instNatCast
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (CombinatorialContracts.leastGridSteps
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
          R)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log R) ε)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) :=
  @CombinatorialContracts.leastGridSteps_add_one_bound

/-- S18: `CombinatorialContracts.leastGridSteps_one`. -/
theorem claim_041 :
  (∀ (q : Real),
  @Eq.{1} Nat
    (CombinatorialContracts.leastGridSteps q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) :=
  @CombinatorialContracts.leastGridSteps_one

/-- S20: `CombinatorialContracts.approximate_clipped_welfare_estimate`. -/
theorem claim_042.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) {τ : Real} {T : Finset.{u_1} ι}
  (hT :
    @CombinatorialContracts.IsApproxBestResponse.{u_1} ι inst inst_1 M τ
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) T),
  And
    (@LE.le.{0} Real Real.instLE
      (@Max.max.{0} Real Real.instMax (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M T)
          (@CombinatorialContracts.Model.cost.{u_1} ι inst inst_1 M T)))
      (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M))
    (@LE.le.{0} Real Real.instLE (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@Max.max.{0} Real Real.instMax (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M T)
            (@CombinatorialContracts.Model.cost.{u_1} ι inst inst_1 M T)))
        τ))) :=
  @CombinatorialContracts.approximate_clipped_welfare_estimate

/-- S20: `CombinatorialContracts.approximate_oracle_robustness`. -/
theorem claim_043.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) {oracle : Nat → Real → Finset.{u_1} ι} {ε τ : Real}
  (ho : @CombinatorialContracts.IsApproxOracle.{u_1} ι inst inst_1 M τ oracle)
  (hε : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
  (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hτ : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) τ),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
        (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          τ)
        ε))
    (@CombinatorialContracts.QueryRecord.utility.{u_1} ι
      (@CombinatorialContracts.OracleRun.output.{u_1} ι
        (@CombinatorialContracts.robustAlgorithm.{u_1} ι inst oracle
          (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M)
          (@CombinatorialContracts.Model.cost.{u_1} ι inst inst_1 M) ε τ)))) :=
  @CombinatorialContracts.approximate_oracle_robustness

/-- S21: `CombinatorialContracts.robust_source_grid_cover`. -/
theorem claim_044 :
  (∀ {ρ R b δ : Real}
  (hρ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ρ)
  (hρ1 : @LT.lt.{0} Real Real.instLT ρ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hR : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) R)
  (hb : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hδ : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ)
  (hlo :
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b
        R)
      δ)
  (hhi : @LE.le.{0} Real Real.instLE δ b),
  @Exists.{1} Nat fun (k : Nat) =>
    And
      (@LT.lt.{0} Nat instLTNat k
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (CombinatorialContracts.leastGridSteps
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ρ)
            R)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (And
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ρ)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            δ)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ρ)
              k)))
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ρ)
              k))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ρ)
            δ)))) :=
  @CombinatorialContracts.robust_source_grid_cover

/-- S21: `CombinatorialContracts.approximate_undershoot_payoff`. -/
theorem claim_045.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) {ε τ δ : Real} {T : Finset.{u_1} ι}
  (hε : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
  (hε1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hτ : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) τ)
  (hP :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M))
  (hlo :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) ε
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@CombinatorialContracts.optimum.{u_1} ι inst inst_1 M)))
      δ)
  (hhi :
    @LE.le.{0} Real Real.instLE δ
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            ε
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@CombinatorialContracts.optimum.{u_1} ι inst inst_1 M))))
  (hT :
    @CombinatorialContracts.IsApproxBestResponse.{u_1} ι inst inst_1 M τ
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) δ)
      T),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
        (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          τ)
        ε))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
      (@CombinatorialContracts.Model.reward.{u_1} ι inst inst_1 M T))) :=
  @CombinatorialContracts.approximate_undershoot_payoff

/-- S22: `CombinatorialContracts.EqualRevenue.binaryIndex_injective`. -/
theorem claim_046 :
  (∀ (n : Nat), @Function.Injective.{1, 1} (Finset.{0} (Fin n)) Nat (@CombinatorialContracts.EqualRevenue.binaryIndex n)) :=
  @CombinatorialContracts.EqualRevenue.binaryIndex_injective

/-- S22: `CombinatorialContracts.EqualRevenue.binaryIndex_surjective`. -/
theorem claim_047 :
  (∀ {n t : Nat}
  (ht :
    @LT.lt.{0} Nat instLTNat t
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)),
  @Exists.{1} (Finset.{0} (Fin n)) fun (S : Finset.{0} (Fin n)) =>
    @Eq.{1} Nat (@CombinatorialContracts.EqualRevenue.binaryIndex n S) t) :=
  @CombinatorialContracts.EqualRevenue.binaryIndex_surjective

/-- S22: `CombinatorialContracts.EqualRevenue.critical_isResponse`. -/
theorem claim_048 :
  (∀ {n : Nat} {S : Finset.{0} (Fin n)}
  (hS :
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@CombinatorialContracts.EqualRevenue.binaryIndex n S)),
  @CombinatorialContracts.IsResponse.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
    (CombinatorialContracts.EqualRevenue.model n)
    (CombinatorialContracts.EqualRevenue.critical (@CombinatorialContracts.EqualRevenue.binaryIndex n S)) S) :=
  @CombinatorialContracts.EqualRevenue.critical_isResponse

/-- S24: `CombinatorialContracts.LowerBounds.unique_optimal_contract`. -/
theorem claim_049 :
  (∀ {n k : Nat} (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
  (hkn :
    @LT.lt.{0} Nat instLTNat k
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
  {α : Real}
  (hopt :
    @Eq.{1} Real
      (@CombinatorialContracts.principal.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
        (CombinatorialContracts.LowerBounds.model n k hk) α)
      (@CombinatorialContracts.optimalValue.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
        (CombinatorialContracts.LowerBounds.model n k hk))),
  @Eq.{1} Real α
    (CombinatorialContracts.LowerBounds.entry k
      (CombinatorialContracts.LowerBounds.perturbation
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      k)) :=
  @CombinatorialContracts.LowerBounds.unique_optimal_contract

/-- S25: `CombinatorialContracts.EqualRevenue.approxSupply_card_le_of_critical_gaps`. -/
theorem claim_050 :
  (∀ {n : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
  (p : Fin n → Real) {σ : Real}
  (hσpos : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) σ)
  (hσ :
    ∀ (t : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
          (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          t →
        @LT.lt.{0} Real Real.instLT σ
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (CombinatorialContracts.EqualRevenue.critical
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (CombinatorialContracts.EqualRevenue.critical t)))),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Finset.{0} (Fin n)) (CombinatorialContracts.EqualRevenue.approxSupply n p σ))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) :=
  @CombinatorialContracts.EqualRevenue.approxSupply_card_le_of_critical_gaps

/-- S25: `CombinatorialContracts.EqualRevenue.approxSupply_card_explicit`. -/
theorem claim_051 :
  (∀ (n : Nat) (p : Fin n → Real),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Finset.{0} (Fin n))
      (CombinatorialContracts.EqualRevenue.approxSupply n p
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 8)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@Nat.cast.{0} Real Real.instNatCast
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) :=
  @CombinatorialContracts.EqualRevenue.approxSupply_card_explicit

/-- S26: `CombinatorialContracts.LowerBounds.compiledPointProgram_probes_le`. -/
theorem claim_052.{u_1} :
  (∀ {α : Type u_1} (n k : Nat) (program : CombinatorialContracts.SupplyProgram.{0, u_1} (Fin n) α),
  @LE.le.{0} Nat instLENat
    (@CombinatorialContracts.OracleIdentification.PointProgram.probes.{0, u_1} Nat α
      (@CombinatorialContracts.OracleIdentification.pointOracle.{0} Nat instDecidableEqNat k)
      (@CombinatorialContracts.LowerBounds.compiledPointProgram.{u_1} α n program))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@List.count.{0} CombinatorialContracts.QueryKind
          (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
          CombinatorialContracts.QueryKind.response
          (@Prod.snd.{u_1, 0} α (List.{0} CombinatorialContracts.QueryKind)
            (@CombinatorialContracts.LowerBounds.execute.{u_1} α n k program))))
      (@List.count.{0} CombinatorialContracts.QueryKind
        (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind CombinatorialContracts.instDecidableEqQueryKind)
        CombinatorialContracts.QueryKind.cost
        (@Prod.snd.{u_1, 0} α (List.{0} CombinatorialContracts.QueryKind)
          (@CombinatorialContracts.LowerBounds.execute.{u_1} α n k program))))) :=
  @CombinatorialContracts.LowerBounds.compiledPointProgram_probes_le

/-- S27: `CombinatorialContracts.OracleIdentification.adaptive_identification`. -/
theorem claim_053.{u_1} :
  (∀ {κ : Type u_1} [inst : DecidableEq.{u_1 + 1} κ] (K : Finset.{u_1} κ) (hK : @Finset.Nonempty.{u_1} κ K)
  (p : CombinatorialContracts.OracleIdentification.PointProgram.{u_1, u_1} κ κ),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{u_1} κ K))
      (@CombinatorialContracts.OracleIdentification.successProbability.{u_1} κ inst K p))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@CombinatorialContracts.OracleIdentification.expectedProbes.{u_1} κ inst K p))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) :=
  @CombinatorialContracts.OracleIdentification.adaptive_identification

/-- S27: `CombinatorialContracts.OracleIdentification.randomized_identification_lintegral`. -/
theorem claim_054.{u_1, u_2} :
  (∀ {κ : Type u_1} [inst : DecidableEq.{u_1 + 1} κ] {Ω : Type u_2} [inst_1 : MeasurableSpace.{u_2} Ω]
  (μ : @MeasureTheory.Measure.{u_2} Ω inst_1) [@MeasureTheory.IsProbabilityMeasure.{u_2} Ω inst_1 μ]
  (K : Finset.{u_1} κ) (hK : @Finset.Nonempty.{u_1} κ K)
  (program : Ω → CombinatorialContracts.OracleIdentification.PointProgram.{u_1, u_1} κ κ),
  @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
      (@instHMul.{0} ENNReal
        (@Distrib.toMul.{0} ENNReal
          (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
              (@Semiring.toNonAssocSemiring.{0} ENNReal
                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
        (@Finset.card.{u_1} κ K))
      (@MeasureTheory.lintegral.{u_2} Ω inst_1 μ fun (ω : Ω) =>
        ENNReal.ofReal (@CombinatorialContracts.OracleIdentification.successProbability.{u_1} κ inst K (program ω))))
    (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal
      (@instHAdd.{0} ENNReal
        (@Distrib.toAdd.{0} ENNReal
          (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
              (@Semiring.toNonAssocSemiring.{0} ENNReal
                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                (@Semiring.toNonAssocSemiring.{0} ENNReal
                  (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@MeasureTheory.lintegral.{u_2} Ω inst_1 μ fun (ω : Ω) =>
          ENNReal.ofReal (@CombinatorialContracts.OracleIdentification.expectedProbes.{u_1} κ inst K (program ω))))
      (@OfNat.ofNat.{0} ENNReal (nat_lit 1)
        (@One.toOfNat1.{0} ENNReal
          (@AddMonoidWithOne.toOne.{0} ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal)))))) :=
  @CombinatorialContracts.OracleIdentification.randomized_identification_lintegral

/-- S28: `CombinatorialContracts.LowerBounds.decodeNat_correct`. -/
theorem claim_055 :
  (∀ {n k : Nat} (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
  (hk :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
      (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
  {α : Real}
  (happrox :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (CombinatorialContracts.LowerBounds.accuracy
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@CombinatorialContracts.optimalValue.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
          (CombinatorialContracts.LowerBounds.instanceAt n k)))
      (@CombinatorialContracts.principal.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
        (CombinatorialContracts.LowerBounds.instanceAt n k) α)),
  @Eq.{1} Nat (CombinatorialContracts.LowerBounds.decodeNat n α) k) :=
  @CombinatorialContracts.LowerBounds.decodeNat_correct

/-- S29: `CombinatorialContracts.eventually_exponential_supply_lower_bound_ennreal`. -/
theorem claim_056 :
  (∀ (Q V : Nat → ENNReal) (δ C : Real) (d : Nat)
  (hδ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ)
  (hqueries :
    @Filter.Eventually.{0} Nat
      (fun (n : Nat) =>
        @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
          (ENNReal.ofReal
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal
            (@instHAdd.{0} ENNReal
              (@Distrib.toAdd.{0} ENNReal
                (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                    (@Semiring.toNonAssocSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
            (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHAdd.{0} ENNReal
                (@Distrib.toAdd.{0} ENNReal
                  (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                      (@Semiring.toNonAssocSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
              (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                        (@Semiring.toNonAssocSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
                (ENNReal.ofReal
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 8)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@Nat.cast.{0} Real Real.instNatCast n)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (Q n))
              (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                        (@Semiring.toNonAssocSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
                (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (V n)))
            (@OfNat.ofNat.{0} ENNReal (nat_lit 1)
              (@One.toOfNat1.{0} ENNReal
                (@AddMonoidWithOne.toOne.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))))))
      (@Filter.atTop.{0} Nat Nat.instPreorder))
  (hpoly :
    @Filter.Eventually.{0} Nat
      (fun (n : Nat) =>
        @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
          (V n)
          (ENNReal.ofReal
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast n)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                d))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)),
  @Filter.Eventually.{0} Nat
    (fun (n : Nat) =>
      @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
        (ENNReal.ofReal
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            n))
        (Q n))
    (@Filter.atTop.{0} Nat Nat.instPreorder)) :=
  @CombinatorialContracts.eventually_exponential_supply_lower_bound_ennreal

/-- S31: `CombinatorialContracts.scaled_response_iff`. -/
theorem claim_057.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) (scale : Real)
  (hscale :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) scale)
  (α : Real) (S : Finset.{u_1} ι),
  Iff
    (@CombinatorialContracts.IsResponse.{u_1} ι inst inst_1
      (@CombinatorialContracts.scaledModel.{u_1} ι inst inst_1 M scale hscale) α S)
    (@CombinatorialContracts.IsResponse.{u_1} ι inst inst_1 M α S)) :=
  @CombinatorialContracts.scaled_response_iff

/-- S31: `CombinatorialContracts.scaled_welfare`. -/
theorem claim_058.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) (scale : Real)
  (hscale :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) scale),
  @Eq.{1} Real
    (@CombinatorialContracts.welfare.{u_1} ι inst inst_1
      (@CombinatorialContracts.scaledModel.{u_1} ι inst inst_1 M scale hscale))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) scale
      (@CombinatorialContracts.welfare.{u_1} ι inst inst_1 M))) :=
  @CombinatorialContracts.scaled_welfare

/-- S31: `CombinatorialContracts.scaled_optimalValue`. -/
theorem claim_059.{u_1} :
  (∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι]
  (M : @CombinatorialContracts.Model.{u_1} ι inst inst_1) (scale : Real)
  (hscale :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) scale),
  @Eq.{1} Real
    (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1
      (@CombinatorialContracts.scaledModel.{u_1} ι inst inst_1 M scale hscale))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) scale
      (@CombinatorialContracts.optimalValue.{u_1} ι inst inst_1 M))) :=
  @CombinatorialContracts.scaled_optimalValue

/-- S31: `CombinatorialContracts.Tightness.Bundle.normalized_localization_ratio`. -/
theorem claim_060 :
  (∀ {m : Nat} {η : Real} (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
  (hη : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) η)
  (hη1 : @LT.lt.{0} Real Real.instLT η (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (i : CombinatorialContracts.Tightness.Bundle.Action m)
  (hi :
    @Membership.mem.{0, 0} (CombinatorialContracts.Tightness.Bundle.Action m)
      (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
      (@Finset.instMembership.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
      (CombinatorialContracts.Tightness.Bundle.A m) i),
  @Eq.{1} Real
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@CombinatorialContracts.welfare.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
        (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
        (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
          @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a b)
        (CombinatorialContracts.Tightness.Bundle.normalizedModel m η hm hη hη1))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) η)
              (@Nat.cast.{0} Real Real.instNatCast m))))
        (@CombinatorialContracts.Model.reward.{0} (CombinatorialContracts.Tightness.Bundle.Action m)
          (@instFintypeSum.{0, 0} (Fin m) (Fin m) (Fin.fintype m) (Fin.fintype m))
          (fun (a b : CombinatorialContracts.Tightness.Bundle.Action m) =>
            @instDecidableEqSum.{0, 0} (Fin m) (Fin m) (instDecidableEqFin m) (instDecidableEqFin m) a b)
          (CombinatorialContracts.Tightness.Bundle.normalizedModel m η hm hη hη1)
          (@Singleton.singleton.{0, 0} (CombinatorialContracts.Tightness.Bundle.Action m)
            (Finset.{0} (CombinatorialContracts.Tightness.Bundle.Action m))
            (@Finset.instSingleton.{0} (CombinatorialContracts.Tightness.Bundle.Action m)) i))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast m)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) η)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast m)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) η))) :=
  @CombinatorialContracts.Tightness.Bundle.normalized_localization_ratio

/-- S32: `CombinatorialContracts.EqualRevenue.harmonic_binary_bounds`. -/
theorem claim_061 :
  (∀ (n : Nat),
  And
    (@LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast n)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (CombinatorialContracts.EqualRevenue.harmonic
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@LE.le.{0} Real Real.instLE
      (CombinatorialContracts.EqualRevenue.harmonic
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Real Real.instNatCast n))) :=
  @CombinatorialContracts.EqualRevenue.harmonic_binary_bounds

/-- S33: `CombinatorialContracts.LowerBounds.exists_finite_program_of_termination`. -/
theorem claim_062.{u_1, u_2, u_3} :
  (∀ {ι : Type u_1} {α : Type u_2} {κ : Type u_3} [DecidableEq.{u_3 + 1} κ]
  (strategy : CombinatorialContracts.LowerBounds.HistoryStrategy.{u_1, u_2} ι α) (fallback : α) (K : Finset.{u_3} κ)
  (supply : κ → (ι → Real) → Finset.{u_1} ι) (value costValue : κ → Finset.{u_1} ι → Real)
  (hterm :
    ∀ (k : κ),
      @Membership.mem.{u_3, u_3} κ (Finset.{u_3} κ) (@Finset.instMembership.{u_3} κ) K k →
        @Exists.{u_2 + 1} (Prod.{u_2, 0} α (List.{0} CombinatorialContracts.QueryKind))
          fun (result : Prod.{u_2, 0} α (List.{0} CombinatorialContracts.QueryKind)) =>
          @CombinatorialContracts.LowerBounds.StrategyTerminatesWith.{u_1, u_2} ι α strategy (supply k) (value k)
            (costValue k) (@List.nil.{u_1} (CombinatorialContracts.LowerBounds.StrategyObservation.{u_1} ι)) result),
  @Exists.{max (u_1 + 1) (u_2 + 1)} (CombinatorialContracts.SupplyProgram.{u_1, u_2} ι α)
    fun (program : CombinatorialContracts.SupplyProgram.{u_1, u_2} ι α) =>
    ∀ (k : κ),
      @Membership.mem.{u_3, u_3} κ (Finset.{u_3} κ) (@Finset.instMembership.{u_3} κ) K k →
        ∀ (result : Prod.{u_2, 0} α (List.{0} CombinatorialContracts.QueryKind)),
          @CombinatorialContracts.LowerBounds.StrategyTerminatesWith.{u_1, u_2} ι α strategy (supply k) (value k)
              (costValue k) (@List.nil.{u_1} (CombinatorialContracts.LowerBounds.StrategyObservation.{u_1} ι)) result →
            @Eq.{u_2 + 1} (Prod.{u_2, 0} α (List.{0} CombinatorialContracts.QueryKind))
              (@CombinatorialContracts.SupplyProgram.eval.{u_1, u_2} ι α (supply k) (value k) (costValue k) program)
              result) :=
  @CombinatorialContracts.LowerBounds.exists_finite_program_of_termination

/-- S34: `CombinatorialContracts.LowerBounds.randomized_high_accuracy_query_bound_lintegral`. -/
theorem claim_063.{u_1} :
  (∀ {Ω : Type u_1} [inst : MeasurableSpace.{u_1} Ω] (μ : @MeasureTheory.Measure.{u_1} Ω inst)
  [@MeasureTheory.IsProbabilityMeasure.{u_1} Ω inst μ] {n : Nat}
  (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
  (program : Ω → CombinatorialContracts.SupplyProgram.{0, 0} (Fin n) Real)
  (hV :
    @Measurable.{u_1, 0} Ω Real inst Real.measurableSpace fun (ω : Ω) =>
      CombinatorialContracts.LowerBounds.expectedValueCalls n (program ω)),
  @LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
      (@instHMul.{0} ENNReal
        (@Distrib.toMul.{0} ENNReal
          (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
              (@Semiring.toNonAssocSemiring.{0} ENNReal
                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
      (@HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal
        (@instHPow.{0, 0} ENNReal Nat
          (@Monoid.toNatPow.{0} ENNReal
            (@MonoidWithZero.toMonoid.{0} ENNReal
              (@Semiring.toMonoidWithZero.{0} ENNReal
                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring)))))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@MeasureTheory.lintegral.{u_1} Ω inst μ fun (ω : Ω) =>
        ENNReal.ofReal (CombinatorialContracts.LowerBounds.approximationProbability n (program ω))))
    (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal
      (@instHAdd.{0} ENNReal
        (@Distrib.toAdd.{0} ENNReal
          (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
              (@Semiring.toNonAssocSemiring.{0} ENNReal
                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                (@Semiring.toNonAssocSemiring.{0} ENNReal
                  (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal
          (@instHAdd.{0} ENNReal
            (@Distrib.toAdd.{0} ENNReal
              (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                  (@Semiring.toNonAssocSemiring.{0} ENNReal
                    (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
            (@instHMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal
                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                    (@Semiring.toNonAssocSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))))
            (@Nat.cast.{0} ENNReal
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            (@MeasureTheory.lintegral.{u_1} Ω inst μ fun (ω : Ω) =>
              ENNReal.ofReal (CombinatorialContracts.LowerBounds.expectedSupplyCalls n (program ω))))
          (@MeasureTheory.lintegral.{u_1} Ω inst μ fun (ω : Ω) =>
            ENNReal.ofReal (CombinatorialContracts.LowerBounds.expectedValueCalls n (program ω)))))
      (@OfNat.ofNat.{0} ENNReal (nat_lit 1)
        (@One.toOfNat1.{0} ENNReal
          (@AddMonoidWithOne.toOne.{0} ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal)))))) :=
  @CombinatorialContracts.LowerBounds.randomized_high_accuracy_query_bound_lintegral

/-- S34: `CombinatorialContracts.LowerBounds.exists_hidden_expected_supply_ge_average_ennreal`. -/
theorem claim_064.{u_1} :
  (∀ {Ω : Type u_1} [inst : MeasurableSpace.{u_1} Ω] (μ : @MeasureTheory.Measure.{u_1} Ω inst) {n : Nat}
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (program : Ω → CombinatorialContracts.SupplyProgram.{0, 0} (Fin n) Real)
  (hQ :
    ∀ (k : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
          (CombinatorialContracts.LowerBounds.hiddenIndices n) k →
        @Measurable.{u_1, 0} Ω Real inst Real.measurableSpace fun (ω : Ω) =>
          @Nat.cast.{0} Real Real.instNatCast
            (@List.count.{0} CombinatorialContracts.QueryKind
              (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                CombinatorialContracts.instDecidableEqQueryKind)
              CombinatorialContracts.QueryKind.response
              (@Prod.snd.{0, 0} Real (List.{0} CombinatorialContracts.QueryKind)
                (@CombinatorialContracts.LowerBounds.execute.{0} Real n k (program ω))))),
  @Exists.{1} Nat fun (k : Nat) =>
    And
      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat) (@Finset.instMembership.{0} Nat)
        (CombinatorialContracts.LowerBounds.hiddenIndices n) k)
      (@LE.le.{0} ENNReal (@Preorder.toLE.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
        (@MeasureTheory.lintegral.{u_1} Ω inst μ fun (ω : Ω) =>
          ENNReal.ofReal (CombinatorialContracts.LowerBounds.expectedSupplyCalls n (program ω)))
        (@MeasureTheory.lintegral.{u_1} Ω inst μ fun (ω : Ω) =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instAddCommMonoidWithOneENNReal))
            (@List.count.{0} CombinatorialContracts.QueryKind
              (@instBEqOfDecidableEq.{0} CombinatorialContracts.QueryKind
                CombinatorialContracts.instDecidableEqQueryKind)
              CombinatorialContracts.QueryKind.response
              (@Prod.snd.{0, 0} Real (List.{0} CombinatorialContracts.QueryKind)
                (@CombinatorialContracts.LowerBounds.execute.{0} Real n k (program ω))))))) :=
  @CombinatorialContracts.LowerBounds.exists_hidden_expected_supply_ge_average_ennreal

end CombinatorialContractsAudit
