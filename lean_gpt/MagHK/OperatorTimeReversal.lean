import MagHK.FermionRealization
import MagHK.TimeReversal
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.OperatorNorm

/-! Literal complex conjugation on the antisymmetric L² space, its transported
operator domain, and covariance of the actual magnetic differential expression.
Only the general antiunitary preservation of selfadjointness, spectrum and
complex multiplicities is left as an explicit universal operator-theory input.
-/
noncomputable section
namespace MagHK.OperatorTimeReversal
open MeasureTheory
open MagHK.Ordering MagHK.TensorRealization MagHK.FermionRealization
open scoped ComplexConjugate ContDiff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem fderiv_conjugate (f : X → ℂ) (x d : X) :
    fderiv ℝ (fun y => conj (f y)) x d = conj (fderiv ℝ f x d) := by
  simpa only [Complex.star_def, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply] using
    congrArg (fun L : X →L[ℝ] ℂ => L d) (fderiv_star (𝕜 := ℝ) (f := f) (x := x))

theorem directional_second_conjugate (f : X → ℂ) (x d : X) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => conj (f z)) y d) x d =
      conj (fderiv ℝ (fun y => fderiv ℝ f y d) x d) := by
  simp_rw [fderiv_conjugate]

theorem differential_covariance (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ)
    (W : ℝ → ℝ) (η : Space → ℂ) (x : Space) :
    TensorRealization.differentialExpression (-A) V W (fun y => conj (η y)) x =
      conj (TensorRealization.differentialExpression A V W η x) := by
  simp only [TensorRealization.differentialExpression, fderiv_conjugate,
    Pi.neg_apply, Prod.fst_neg, Prod.snd_neg,
    neg_sq, map_add, map_sub, map_mul, map_neg, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg, map_ofNat]
  ring

theorem fermion_differential_covariance (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ)
    (W : ℝ → ℝ) (η : Space × Space → ℂ) (p : Space × Space) :
    FermionRealization.differentialExpression (-A) V W (fun q => conj (η q)) p =
      conj (FermionRealization.differentialExpression A V W η p) := by
  unfold FermionRealization.differentialExpression
  rw [differential_covariance, differential_covariance, map_add]

def pairConjugation : PairState →L[ℝ] PairState :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 volume

theorem pairConjugation_ae (ψ : PairState) :
    ∀ᵐ p, pairConjugation ψ p = conj (ψ p) := by
  simpa only [pairConjugation, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using!
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLpL (p := 2) ψ

theorem pairConjugation_involutive (ψ : PairState) :
    pairConjugation (pairConjugation ψ) = ψ := by
  apply Lp.ext
  filter_upwards [pairConjugation_ae (pairConjugation ψ), pairConjugation_ae ψ] with p hp hq
  rw [hp, hq, Complex.conj_conj]

theorem pairConjugation_norm (ψ : PairState) : ‖pairConjugation ψ‖ = ‖ψ‖ := by
  have h (φ : PairState) : ‖pairConjugation φ‖ ≤ ‖φ‖ := by
    have hi := (Complex.conjCLE : ℂ →L[ℝ] ℂ).norm_compLp_le φ
    simpa only [Complex.conjCLE_norm, one_mul] using! hi
  apply le_antisymm (h ψ)
  simpa only [pairConjugation_involutive] using h (pairConjugation ψ)

theorem pairConjugation_swap (ψ : PairState) :
    pairConjugation (swap ψ) = swap (pairConjugation ψ) := by
  apply Lp.ext
  have hs (φ : PairState) : ∀ᵐ p, swap φ p = φ p.swap :=
    Lp.coeFn_compMeasurePreserving φ Measure.measurePreserving_swap
  have hk := Measure.measurePreserving_swap.quasiMeasurePreserving.ae (pairConjugation_ae ψ)
  filter_upwards [pairConjugation_ae (swap ψ), hs ψ, hs (pairConjugation ψ), hk] with p hp hq hr hk
  rw [hp, hq, hr, hk]

theorem pairConjugation_preserves (ψ : PairState) (hψ : ψ ∈ fermionSubspace) :
    pairConjugation ψ ∈ fermionSubspace := by
  change swap (pairConjugation ψ) + pairConjugation ψ = 0
  rw [← pairConjugation_swap, ← map_add]
  change swap ψ + ψ = 0 at hψ
  rw [hψ, map_zero]

def conjugation : FermionState ≃ₗᵢ[ℝ] FermionState where
  toFun ψ := ⟨pairConjugation ψ, pairConjugation_preserves ψ ψ.property⟩
  invFun ψ := ⟨pairConjugation ψ, pairConjugation_preserves ψ ψ.property⟩
  left_inv ψ := Subtype.ext (pairConjugation_involutive ψ)
  right_inv ψ := Subtype.ext (pairConjugation_involutive ψ)
  map_add' ψ φ := Subtype.ext (map_add pairConjugation (ψ : PairState) (φ : PairState))
  map_smul' c ψ := Subtype.ext (map_smul pairConjugation c (ψ : PairState))
  norm_map' ψ := pairConjugation_norm ψ

theorem conjugation_ae (ψ : FermionState) :
    ∀ᵐ p, (conjugation ψ : PairState) p = conj ((ψ : PairState) p) :=
  pairConjugation_ae ψ

@[simp] theorem conjugation_involutive (ψ : FermionState) : conjugation (conjugation ψ) = ψ :=
  Subtype.ext (pairConjugation_involutive ψ)

theorem conjugation_complex_smul (c : ℂ) (ψ : FermionState) :
    conjugation (c • ψ) = conj c • conjugation ψ := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [conjugation_ae (c • ψ), conjugation_ae ψ,
    Lp.coeFn_smul c (ψ : PairState), Lp.coeFn_smul (conj c) (conjugation ψ : PairState)]
      with p hp hq hr hs
  change (conjugation (c • ψ) : PairState) p = (conj c • (conjugation ψ : PairState)) p
  rw [hp]
  change conj ((c • (ψ : PairState)) p) = (conj c • (conjugation ψ : PairState)) p
  rw [hr, hs]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, hq]

/-- The transported domain is the literal inverse image under conjugation. -/
def reverseOperator (F : FermionRealization.System) : FermionRealization.System where
  domain := F.domain.comap conjugation.toLinearEquiv.toLinearMap
  map :=
    { toFun := fun ψ => conjugation (F.map ⟨conjugation ψ, ψ.property⟩)
      map_add' := by
        intro ψ φ
        simp only [Submodule.coe_add, map_add]
        change conjugation (F.map (⟨conjugation ψ, ψ.property⟩ +
          ⟨conjugation φ, φ.property⟩)) = _
        rw [map_add, map_add]
      map_smul' := by
        intro c ψ
        simp only [Submodule.coe_smul, map_smul]
        change conjugation (F.map (c • ⟨conjugation ψ, ψ.property⟩)) = _
        rw [map_smul, map_smul]
        rfl }

theorem reverse_domain (F : FermionRealization.System) (ψ : FermionState)
    (hψ : ψ ∈ F.domain) : conjugation ψ ∈ (reverseOperator F).domain := by
  change conjugation (conjugation ψ) ∈ F.domain
  simpa only [conjugation_involutive] using hψ

theorem reverse_action (F : FermionRealization.System) (ψ : FermionState)
    (hψ : ψ ∈ F.domain) :
    (reverseOperator F).map ⟨conjugation ψ, reverse_domain F ψ hψ⟩ =
      conjugation (F.map ⟨ψ, hψ⟩) := by
  change conjugation (F.map ⟨conjugation (conjugation ψ), _⟩) = _
  simp only [conjugation_involutive]

theorem reverse_eigen (F : FermionRealization.System) (E : ℝ) (ψ : FermionState)
    (h : OperatorModel.Eigen F E ψ) : OperatorModel.Eigen (reverseOperator F) E (conjugation ψ) := by
  obtain ⟨hd, hn, he⟩ := h
  refine ⟨reverse_domain F ψ hd, ?_, ?_⟩
  · exact fun hz => hn (conjugation.injective (by simpa only [map_zero] using hz))
  · rw [reverse_action F ψ hd, he, map_smul]

/-- General antiunitary operator facts for every selfadjoint operator on the
actual fermionic Hilbert space. The transported operator and antiunitary are
already defined above, so no chosen-example spectral conclusion is assumed. -/
def StandardAntiunitaryLibrary : Prop :=
  ∀ F : FermionRealization.System, OperatorModel.SelfAdjoint F →
    OperatorModel.SelfAdjoint (reverseOperator F) ∧
    OperatorModel.spectrum (reverseOperator F) = OperatorModel.spectrum F ∧
    OperatorModel.multiplicity (reverseOperator F) = OperatorModel.multiplicity F

theorem reverse_ground (library : StandardAntiunitaryLibrary)
    (F : FermionRealization.System) (hF : OperatorModel.SelfAdjoint F)
    (E : ℝ) (f : Space × Space → ℂ) (h : GroundState F E f) :
    GroundState (reverseOperator F) E (fun p => conj (f p)) := by
  obtain ⟨_, hs, hm⟩ := library F hF
  rcases h with ⟨⟨ψ, hp, he⟩, hb, hdim, ε, hε, hi⟩
  refine ⟨⟨conjugation ψ, ?_, reverse_eigen F E ψ he⟩, ?_, ?_, ε, hε, ?_⟩
  · filter_upwards [conjugation_ae ψ, hp] with p hp hq
    rw [hp, hq]
  · simpa only [hs] using hb
  · simpa only [hm] using hdim
  · simpa only [hs] using hi

/-- The physical weak equation follows from the actual test-function action
and selfadjointness. This avoids treating a totalized integral identity alone
as the definition of the Hamiltonian. -/
theorem weak_equation_of_test_action (F : FermionRealization.System)
    (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ)
    (hF : OperatorModel.SelfAdjoint F)
    (ht : ∀ η : Space × Space → ℂ,
      ContDiff ℝ ∞ η → HasCompactSupport η → (∀ x y, η (y, x) = -η (x, y)) →
      ∃ φ : FermionState, (∀ᵐ p, (φ : PairState) p = η p) ∧ ∃ hφ : φ ∈ F.domain,
        ∀ᵐ p, ((F.map ⟨φ, hφ⟩ : FermionState) : PairState) p =
          FermionRealization.differentialExpression A V W η p)
    (ψ : FermionState) (hψ : ψ ∈ F.domain) (η : Space × Space → ℂ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (ha : ∀ x y, η (y, x) = -η (x, y)) :
    (∫ p, conj (η p) * ((F.map ⟨ψ, hψ⟩ : FermionState) : PairState) p) =
      ∫ p, conj (FermionRealization.differentialExpression A V W η p) * (ψ : PairState) p := by
  obtain ⟨φ, hp, hφ, hact⟩ := ht η hη hc ha
  have hsym := ((hF.2.2.2 ψ (F.map ⟨ψ, hψ⟩)).mp ⟨hψ, rfl⟩) φ hφ
  calc
    _ = inner ℂ φ (F.map ⟨ψ, hψ⟩) := by
      change _ = inner ℂ (φ : PairState) ((F.map ⟨ψ, hψ⟩ : FermionState) : PairState)
      rw [L2.inner_def]
      simp only [RCLike.inner_apply']
      apply integral_congr_ae
      filter_upwards [hp] with p hp
      rw [hp]
    _ = inner ℂ (F.map ⟨φ, hφ⟩) ψ := hsym.symm
    _ = _ := by
      change inner ℂ ((F.map ⟨φ, hφ⟩ : FermionState) : PairState) (ψ : PairState) = _
      rw [L2.inner_def]
      simp only [RCLike.inner_apply']
      apply integral_congr_ae
      filter_upwards [hact] with p hp
      rw [hp]

/-- Domain transport and differential covariance realize the reversed physical
Hamiltonian. No chosen ground state or energy is used here. -/
theorem reverse_facts (library : StandardAntiunitaryLibrary)
    (F : FermionRealization.System) (A : ℝ × ℝ → ℝ × ℝ)
    (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (hF : FermionRealization.Facts F A V W) :
    FermionRealization.Facts (reverseOperator F) (-A) V W := by
  have hself := (library F hF.selfadjoint).1
  have ht : ∀ η : Space × Space → ℂ,
      ContDiff ℝ ∞ η → HasCompactSupport η → (∀ x y, η (y, x) = -η (x, y)) →
      ∃ ψ : FermionState, (∀ᵐ p, (ψ : PairState) p = η p) ∧
        ∃ hψ : ψ ∈ (reverseOperator F).domain,
        ∀ᵐ p, (((reverseOperator F).map ⟨ψ, hψ⟩ : FermionState) : PairState) p =
          FermionRealization.differentialExpression (-A) V W η p := by
    intro η hη hc ha
    have hηc : ContDiff ℝ ∞ (fun p => conj (η p)) := Complex.conjCLE.contDiff.comp hη
    have hcc : HasCompactSupport (fun p => conj (η p)) := hc.comp_left (map_zero conj)
    have hac : ∀ x y, conj (η (y, x)) = -conj (η (x, y)) := by
      intro x y
      rw [ha, map_neg]
    obtain ⟨ψ, hp, hd, hact⟩ := hF.test_action (fun p => conj (η p)) hηc hcc hac
    refine ⟨conjugation ψ, ?_, reverse_domain F ψ hd, ?_⟩
    · filter_upwards [conjugation_ae ψ, hp] with p hp hq
      rw [hp, hq, Complex.conj_conj]
    · rw [reverse_action F ψ hd]
      filter_upwards [conjugation_ae (F.map ⟨ψ, hd⟩), hact] with p hp hq
      rw [hp, hq]
      simpa only [Complex.conj_conj] using
        (fermion_differential_covariance A V W (fun q => conj (η q)) p).symm
  exact ⟨hself, ht, weak_equation_of_test_action (reverseOperator F) (-A) V W hself ht⟩

end MagHK.OperatorTimeReversal
