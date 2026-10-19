import MagHK.MonopoleOccupied
import MagHK.MonopoleGround
import MagHK.MonopoleCurrent
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.OperatorNorm

/-! Actual complex conjugation of monopole sections and their operator domains.
Local expression and form covariance are checked before the universal
Friedrichs and antiunitary operator transport premises are applied. -/
noncomputable section
namespace MagHK.MonopoleTimeReversal
open MeasureTheory Set Filter
open MagHK.Ordering MagHK.MonopoleRealization MagHK.MonopoleAngular
open scoped ComplexConjugate ContDiff Topology

theorem transition_conjugate (q : ℤ) (φ : ℝ) :
    transition (-q) φ = conj (transition q φ) := by
  unfold transition
  rw [← Complex.exp_conj]
  congr 1
  simp only [Int.cast_neg, Complex.ofReal_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem southRepresentative_conjugate (q : ℤ) (f : Chart → ℂ) (x : Chart) :
    southRepresentative (-q) (fun y => conj (f y)) x = conj (southRepresentative q f x) := by
  simp only [southRepresentative, transition_conjugate, map_mul]

theorem deriv_conjugate (f : ℝ → ℂ) (r : ℝ) :
    deriv (fun s => conj (f s)) r = conj (deriv f r) := by
  simpa only [Complex.star_def] using (deriv.star (f := f) (x := r))

theorem Dr_conjugate (f : Chart → ℂ) (x : Chart) :
    Dr (fun y => conj (f y)) x = conj (Dr f x) := deriv_conjugate _ _

theorem Dmu_conjugate (f : Chart → ℂ) (x : Chart) :
    Dmu (fun y => conj (f y)) x = conj (Dmu f x) := deriv_conjugate _ _

theorem Dphi_conjugate (f : Chart → ℂ) (x : Chart) :
    Dphi (fun y => conj (f y)) x = conj (Dphi f x) := deriv_conjugate _ _

theorem magneticPhi_conjugate (q : ℤ) (f : Chart → ℂ) (x : Chart) :
    magneticPhi (-q) (fun y => conj (f y)) x = -conj (magneticPhi q f x) := by
  have hn : northCoefficient (-q) x.2.1 = -northCoefficient q x.2.1 := by
    unfold northCoefficient
    push_cast
    ring
  simp only [magneticPhi, Dphi_conjugate, hn, Complex.ofReal_neg,
    map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem formDensity_conjugate (q : ℤ) (f g : Chart → ℂ) (x : Chart) :
    formDensity (-q) (fun y => conj (f y)) (fun y => conj (g y)) x =
      conj (formDensity q f g x) := by
  simp only [formDensity, Dr_conjugate, Dmu_conjugate, magneticPhi_conjugate,
    map_add, map_mul, map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem pairForm_conjugate (q : ℤ) (W : Chart × Chart → ℝ)
    (f g : Chart × Chart → ℂ) :
    pairForm (-q) W (fun p => conj (f p)) (fun p => conj (g p)) =
      conj (pairForm q W f g) := by
  unfold pairForm
  rw [← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    dsimp only
    rw [formDensity_conjugate, formDensity_conjugate]
    simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal])

theorem pairCore_conjugate (f : Chart × Chart → ℂ) (hf : PairCore f) :
    PairCore (fun p => conj (f p)) := by
  rcases hf with ⟨hs, ha, hp, δ, R, hδ, hsupport⟩
  refine ⟨Complex.conjCLE.contDiff.comp hs, ?_, ?_, δ, R, hδ, ?_⟩
  · intro x y
    change conj (f (y, x)) = -conj (f (x, y))
    rw [ha, map_neg]
  · intro r μ y φ
    exact congrArg conj (hp r μ y φ)
  · intro p hp
    exact hsupport p (fun hz => hp (by simp [hz]))

def oneConjugation : State →L[ℝ] State :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 chartMeasure

theorem oneConjugation_ae (f : State) :
    ∀ᵐ x ∂chartMeasure, oneConjugation f x = conj (f x) := by
  simpa only [oneConjugation, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using!
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLpL (p := 2) f

theorem oneConjugation_inner (f g : State) :
    inner ℂ (oneConjugation f) (oneConjugation g) = conj (inner ℂ f g) := by
  rw [MagHK.MonopoleOccupied.inner_integral, MagHK.MonopoleOccupied.inner_integral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [oneConjugation_ae f, oneConjugation_ae g] with x hf hg
  rw [hf, hg]
  simp only [map_mul, Complex.conj_conj]

theorem oneConjugation_orthonormal (f g : State) (hfg : Orthonormal ℂ ![f, g]) :
    Orthonormal ℂ ![oneConjugation f, oneConjugation g] := by
  rw [orthonormal_iff_ite] at hfg ⊢
  have h00 : inner ℂ f f = 1 := by simpa using hfg 0 0
  have h01 : inner ℂ f g = 0 := by simpa using hfg 0 1
  have h10 : inner ℂ g f = 0 := by simpa using hfg 1 0
  have h11 : inner ℂ g g = 1 := by simpa using hfg 1 1
  intro i j
  fin_cases i <;> fin_cases j
  · change inner ℂ (oneConjugation f) (oneConjugation f) = 1
    rw [oneConjugation_inner, h00, map_one]
  · change inner ℂ (oneConjugation f) (oneConjugation g) = 0
    rw [oneConjugation_inner, h01, map_zero]
  · change inner ℂ (oneConjugation g) (oneConjugation f) = 0
    rw [oneConjugation_inner, h10, map_zero]
  · change inner ℂ (oneConjugation g) (oneConjugation g) = 1
    rw [oneConjugation_inner, h11, map_one]

def pairConjugation : PairState →L[ℝ] PairState :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 pairMeasure

theorem pairConjugation_ae (ψ : PairState) :
    ∀ᵐ p ∂pairMeasure, pairConjugation ψ p = conj (ψ p) := by
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
  have hs (φ : PairState) : ∀ᵐ p ∂pairMeasure, swap φ p = φ p.swap :=
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
    ∀ᵐ p ∂pairMeasure, (conjugation ψ : PairState) p = conj ((ψ : PairState) p) :=
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
def reverseOperator (F : FermionSystem) : FermionSystem where
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

theorem reverse_domain (F : FermionSystem) (ψ : FermionState)
    (hψ : ψ ∈ F.domain) : conjugation ψ ∈ (reverseOperator F).domain := by
  change conjugation (conjugation ψ) ∈ F.domain
  simpa only [conjugation_involutive] using hψ

theorem reverse_action (F : FermionSystem) (ψ : FermionState)
    (hψ : ψ ∈ F.domain) :
    (reverseOperator F).map ⟨conjugation ψ, reverse_domain F ψ hψ⟩ =
      conjugation (F.map ⟨ψ, hψ⟩) := by
  change conjugation (F.map ⟨conjugation (conjugation ψ), _⟩) = _
  simp only [conjugation_involutive]

theorem reverse_eigen (F : FermionSystem) (E : ℝ) (ψ : FermionState)
    (h : OperatorModel.Eigen F E ψ) : OperatorModel.Eigen (reverseOperator F) E (conjugation ψ) := by
  obtain ⟨hd, hn, he⟩ := h
  refine ⟨reverse_domain F ψ hd, ?_, ?_⟩
  · exact fun hz => hn (conjugation.injective (by simpa only [map_zero] using hz))
  · rw [reverse_action F ψ hd, he, map_smul]

theorem determinant_conjugate (f g : Chart → ℂ) (p : Chart × Chart) :
    determinant (fun x => conj (f x)) (fun x => conj (g x)) p =
      conj (determinant f g p) := by
  simp only [determinant, MagHK.Slater.slaterSlice, MagHK.Slater.determinantSlice,
    MagHK.Slater.scale, map_mul, map_sub, map_inv₀, Complex.conj_ofReal]

theorem IsSlater.conjugate (ψ : FermionState) (hψ : IsSlater ψ) : IsSlater (conjugation ψ) := by
  obtain ⟨f, g, hfg, hrep⟩ := hψ
  refine ⟨oneConjugation f, oneConjugation g, oneConjugation_orthonormal f g hfg, ?_⟩
  filter_upwards [conjugation_ae ψ, hrep,
    Measure.quasiMeasurePreserving_fst.ae (oneConjugation_ae f),
    Measure.quasiMeasurePreserving_snd.ae (oneConjugation_ae f),
    Measure.quasiMeasurePreserving_fst.ae (oneConjugation_ae g),
    Measure.quasiMeasurePreserving_snd.ae (oneConjugation_ae g)] with p hp hr hf1 hf2 hg1 hg2
  rw [hp, hr]
  rw [← determinant_conjugate]
  unfold determinant MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
  rw [hf1, hf2, hg1, hg2]

theorem isSlater_conjugate_iff (ψ : FermionState) : IsSlater (conjugation ψ) ↔ IsSlater ψ := by
  constructor
  · intro h
    simpa only [conjugation_involutive] using IsSlater.conjugate (conjugation ψ) h
  · exact IsSlater.conjugate ψ

def density (ψ : FermionState) (x : Chart) : ℝ :=
  2 * ∫ y, Complex.normSq ((ψ : PairState) (x, y)) ∂chartMeasure

theorem density_conjugate (ψ : FermionState) :
    density (conjugation ψ) =ᵐ[chartMeasure] density ψ := by
  have hp : (fun p => Complex.normSq ((conjugation ψ : PairState) p)) =ᵐ[pairMeasure]
      (fun p => Complex.normSq ((ψ : PairState) p)) := by
    filter_upwards [conjugation_ae ψ] with p hp
    rw [hp, Complex.normSq_conj]
  have h := Measure.ae_ae_of_ae_prod hp
  filter_upwards [h] with x hx
  exact congrArg (fun r : ℝ => 2 * r) (integral_congr_ae hx)

/-- Uniform antiunitary spectral transport on the literal inverse-image
operator domain. It has no charge or selected-state conclusion. -/
def StandardAntiunitaryLibrary : Prop :=
  ∀ F : FermionSystem, OperatorModel.SelfAdjoint F →
    OperatorModel.spectrum (reverseOperator F) = OperatorModel.spectrum F ∧
    OperatorModel.multiplicity (reverseOperator F) = OperatorModel.multiplicity F

structure FormTransport (S S' : MagneticFormSystem) : Prop where
  represented : ∀ ψ : S.domain, ∃ ζ : S'.domain,
    (ζ : PairState) = pairConjugation (ψ : PairState) ∧
      ∀ i k, S'.pi i k ζ = -pairConjugation (S.pi i k ψ)

/-- General conjugation transport of a closed magnetic form and its weak
derivatives. The exact core and form identities are separate hypotheses and
are proved above for all integral charges and all real scalar potentials.
This is the Friedrichs representation theorem and closed Sobolev product
rule under an antiunitary, with no selected state or current premise. -/
def StandardFriedrichsConjugationLibrary : Prop :=
  ∀ (q : ℤ) W (F : FermionSystem),
    (∀ f, PairCore f → PairCore (fun p => conj (f p))) →
    (∀ f g, pairForm (-q) W (fun p => conj (f p)) (fun p => conj (g p)) =
      conj (pairForm q W f g)) →
    FermionFacts F q W →
    FermionFacts (reverseOperator F) (-q) W ∧
      ∀ S : MagneticFormSystem, MagneticFormFacts S F q W →
        ∃ S' : MagneticFormSystem, MagneticFormFacts S' (reverseOperator F) (-q) W ∧ FormTransport S S'

theorem reverse_facts (library : StandardFriedrichsConjugationLibrary)
    (q : ℤ) (W : Chart × Chart → ℝ) (F : FermionSystem) (hF : FermionFacts F q W) :
    FermionFacts (reverseOperator F) (-q) W ∧
      ∀ S : MagneticFormSystem, MagneticFormFacts S F q W →
        ∃ S' : MagneticFormSystem, MagneticFormFacts S' (reverseOperator F) (-q) W ∧ FormTransport S S' :=
  library q W F pairCore_conjugate (pairForm_conjugate q W) hF

theorem reverse_ground (library : StandardAntiunitaryLibrary)
    (F : FermionSystem) (hF : OperatorModel.SelfAdjoint F) (E : ℝ)
    (f : Chart × Chart → ℂ) (h : GroundState F E f) :
    GroundState (reverseOperator F) E (fun p => conj (f p)) := by
  obtain ⟨hs, hm⟩ := library F hF
  rcases h with ⟨⟨ψ, hp, he⟩, hb, hdim⟩
  refine ⟨⟨conjugation ψ, ?_, reverse_eigen F E ψ he⟩, ?_, ?_⟩
  · filter_upwards [conjugation_ae ψ, hp] with p hp hq
    rw [hp, hq]
  · simpa only [hs] using hb
  · simpa only [hm] using hdim

theorem reverse_gap (library : StandardAntiunitaryLibrary)
    (F : FermionSystem) (hF : OperatorModel.SelfAdjoint F) (E δ : ℝ)
    (h : SpectralGap F E δ) : SpectralGap (reverseOperator F) E δ := by
  simpa only [SpectralGap, (library F hF).1] using h

theorem pairCurrent_reverse (S S' : MagneticFormSystem) (ψ : S.domain) (ζ : S'.domain)
    (hψ : (ζ : PairState) = pairConjugation (ψ : PairState))
    (hpi : ∀ i k, S'.pi i k ζ = -pairConjugation (S.pi i k ψ)) :
    MagHK.MonopoleCurrent.pairCurrent S' ζ =ᵐ[pairMeasure]
      fun p => -MagHK.MonopoleCurrent.pairCurrent S ψ p := by
  have hp : ∀ᵐ p ∂pairMeasure, (ζ : PairState) p = conj ((ψ : PairState) p) := by
    rw [hψ]
    exact pairConjugation_ae _
  have hk : ∀ᵐ p ∂pairMeasure, ∀ k : Fin 3, S'.pi 0 k ζ p = -conj (S.pi 0 k ψ p) := by
    rw [ae_all_iff]
    intro k
    rw [hpi]
    filter_upwards [Lp.coeFn_neg (pairConjugation (S.pi 0 k ψ)), pairConjugation_ae (S.pi 0 k ψ)] with p hn hc
    rw [hn]
    change -pairConjugation (S.pi 0 k ψ) p = -conj (S.pi 0 k ψ p)
    rw [hc]
  have he (a b : ℂ) : (conj (conj a) * (-conj b)).re = -(conj a * b).re := by
    simp only [Complex.conj_conj, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im]
    ring
  filter_upwards [hp, hk] with p hp hk
  simp only [MagHK.MonopoleCurrent.pairCurrent, hp, hk, he, neg_smul, Finset.sum_neg_distrib]

theorem current_reverse (S S' : MagneticFormSystem) (ψ : S.domain) (ζ : S'.domain)
    (hψ : (ζ : PairState) = pairConjugation (ψ : PairState))
    (hpi : ∀ i k, S'.pi i k ζ = -pairConjugation (S.pi i k ψ)) :
    MagHK.MonopoleCurrent.current S' ζ =ᵐ[chartMeasure]
      fun x => -MagHK.MonopoleCurrent.current S ψ x := by
  have h := Measure.ae_ae_of_ae_prod (pairCurrent_reverse S S' ψ ζ hψ hpi)
  filter_upwards [h] with x hx
  simp only [MagHK.MonopoleCurrent.current]
  rw [integral_congr_ae hx, integral_neg, smul_neg]

/-- Transport of an arbitrary normalized correlated ground state to the
opposite charge. All selected-state inputs concern only the original charge.
The reversed state, operator domain, density, current and Slater obstruction
are obtained by the concrete conjugation proved in this module. -/
theorem opposite_charge_of_ground
    (spectral : StandardAntiunitaryLibrary) (friedrichs : StandardFriedrichsConjugationLibrary)
    (q : ℤ) (W : Chart × Chart → ℝ) (F : FermionSystem) (E δ : ℝ)
    (ψ : FermionState) (S : MagneticFormSystem) (u : S.domain)
    (hF : FermionFacts F q W) (hS : MagneticFormFacts S F q W)
    (hu : (u : PairState) = (ψ : PairState))
    (hE : OperatorModel.Eigen F E ψ) (hn : ‖ψ‖ = 1)
    (hg : GroundState F E (fun p => (ψ : PairState) p)) (hgap : SpectralGap F E δ)
    (hns : ¬ IsSlater ψ) (hj : ∀ᵐ x ∂chartMeasure, MagHK.MonopoleCurrent.current S u x = 0) :
    FermionFacts (reverseOperator F) (-q) W ∧
      OperatorModel.Eigen (reverseOperator F) E (conjugation ψ) ∧ ‖conjugation ψ‖ = 1 ∧
      GroundState (reverseOperator F) E (fun p => (conjugation ψ : PairState) p) ∧
      SpectralGap (reverseOperator F) E δ ∧ ¬ IsSlater (conjugation ψ) ∧
      density (conjugation ψ) =ᵐ[chartMeasure] density ψ ∧
      ∃ S' : MagneticFormSystem, ∃ ζ : S'.domain,
        MagneticFormFacts S' (reverseOperator F) (-q) W ∧
        (ζ : PairState) = (conjugation ψ : PairState) ∧
        ∀ᵐ x ∂chartMeasure, MagHK.MonopoleCurrent.current S' ζ x = 0 := by
  obtain ⟨hF', hforms⟩ := reverse_facts friedrichs q W F hF
  obtain ⟨S', hS', ht⟩ := hforms S hS
  obtain ⟨ζ, hζ, hpi⟩ := ht.represented u
  have he := reverse_eigen F E ψ hE
  obtain ⟨hspec, hmult⟩ := spectral F hF.selfadjoint
  refine ⟨hF', he, (conjugation.norm_map ψ).trans hn,
    ⟨⟨conjugation ψ, ae_of_all _ (fun _ => rfl), he⟩, ?_, ?_⟩,
    reverse_gap spectral F hF.selfadjoint E δ hgap,
    (fun h => hns ((isSlater_conjugate_iff ψ).mp h)), density_conjugate ψ,
    S', ζ, hS', ?_, ?_⟩
  · simpa only [hspec] using hg.2.1
  · simpa only [hmult] using hg.2.2
  · rw [hζ, hu]
    rfl
  · have hc := current_reverse S S' u ζ hζ hpi
    filter_upwards [hc, hj] with x hx hz
    rw [hx, hz, neg_zero]


end MagHK.MonopoleTimeReversal
