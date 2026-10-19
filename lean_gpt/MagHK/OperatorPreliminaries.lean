import MagHK.FermionRealization
import Mathlib.LinearAlgebra.Dimension.Free

/-!
Exact essential spectra and Sobolev domains for the bounded construction.
The essential spectrum removes actual isolated eigenvalues of finite complex
multiplicity from the bounded-inverse spectrum. Sobolev membership means
existence of literal distributional partial derivatives in Lebesgue L².
The form domain is the completion of the actual operator domain in a shifted
quadratic-form norm, rather than an unrelated set of test functions.

The external libraries below are general Weyl, tensor essential-spectrum,
and bounded-coefficient Kato–Rellich theorems. They quantify over arbitrary
coefficients and the same selfadjoint differential realizations used elsewhere.
The manuscript profiles, thresholds and domain identifications are applications.
-/
noncomputable section
namespace MagHK.OperatorPreliminaries
open MeasureTheory Set Filter
open MagHK.Ordering MagHK.OperatorModel
open scoped ContDiff Topology ComplexConjugate

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedSpace ℝ H]

def DiscreteEigenvalue (T : DomainOperator H) (E : ℝ) : Prop :=
  (∃ ψ, Eigen T E ψ) ∧ Module.Finite ℂ (eigenspace T E) ∧
  ∃ ε : ℝ, 0 < ε ∧ ∀ e ∈ spectrum T, |e - E| < ε → e = E

def essentialSpectrum (T : DomainOperator H) : Set ℝ :=
  spectrum T \ {E | DiscreteEigenvalue T E}

/-- Completion in the positive form norm of a lower-semibounded operator.
The shift is existential and does not change this domain. -/
def FormDomain (T : DomainOperator H) : Set H := {ψ |
  ∃ b : ℝ, (∀ u : T.domain, -b * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (T.map u)).re) ∧
  ∃ u : ℕ → T.domain, Tendsto (fun n => (u n : H)) atTop (𝓝 ψ) ∧
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
    |(inner ℂ ((u n - u m : T.domain) : H) (T.map (u n - u m))).re +
      (b + 1) * ‖((u n - u m : T.domain) : H)‖ ^ 2| < ε}
end Abstract

section Sobolev
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasureSpace X] [BorelSpace X]

def WeakPartial (e : X) (f g : X → ℂ) : Prop :=
  ∀ η : X → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
    (∫ x, f x * fderiv ℝ η x e) = -(∫ x, g x * η x)

def SobolevOne {n : ℕ} (e : Fin n → X) (ψ : Lp ℂ 2 (volume : Measure X)) : Prop :=
  ∃ d : Fin n → Lp ℂ 2 (volume : Measure X), ∀ i, WeakPartial (e i) ψ (d i)

def SobolevTwo {n : ℕ} (e : Fin n → X) (ψ : Lp ℂ 2 (volume : Measure X)) : Prop :=
  ∃ d : Fin n → Lp ℂ 2 (volume : Measure X),
    (∀ i, WeakPartial (e i) ψ (d i)) ∧ ∀ i, SobolevOne e (d i)
end Sobolev

def planarDirections : Fin 2 → ℂ := ![1, Complex.I]
def axialDirections : Fin 1 → ℝ := ![1]
def spatialDirections : Fin 3 → TensorRealization.Space :=
  ![(1, 0), (Complex.I, 0), (0, 1)]
def pairDirections : Fin 6 → TensorRealization.Space × TensorRealization.Space :=
  ![((1, 0), 0), ((Complex.I, 0), 0), ((0, 1), 0),
    (0, (1, 0)), (0, (Complex.I, 0)), (0, (0, 1))]

/-- General bounded-coefficient domain theorem. The radial Cartesian
coefficient condition ensures the divergence-free magnetic convention in the
literal differential expressions. No bound on derivatives of A is required.
All four conclusions refer to the actual selfadjoint operators and forms. -/
structure StandardKatoRellichLibrary : Prop where
  planar : ∀ P a v U A V,
    PlanarSpectralLibrary.PlanarCoefficients a v A V →
    (∃ C : ℝ, ∀ p, |V p| ≤ C) → PlanarSpectralLibrary.Facts P a v U A V →
    (∀ ψ, ψ ∈ P.H.domain ↔ SobolevTwo planarDirections ψ) ∧
    (∀ ψ, ψ ∈ FormDomain P.H ↔ SobolevOne planarDirections ψ)
  axial : ∀ Z U V, AxialRealization.Coefficients U V → AxialRealization.Facts Z U V →
    (∀ ψ, ψ ∈ Z.H.domain ↔ SobolevTwo axialDirections ψ) ∧
    (∀ ψ, ψ ∈ FormDomain Z.H ↔ SobolevOne axialDirections ψ)
  tensor : ∀ T a v A V W,
    PlanarSpectralLibrary.PlanarCoefficients a v A V →
    (∃ C : ℝ, ∀ p, |V p| ≤ C) → ContDiff ℝ ∞ W →
    (∃ C : ℝ, ∀ z, |W z| ≤ C) → FermionRealization.OneBodyRealization T A V W →
    (∀ ψ, ψ ∈ T.domain ↔ SobolevTwo spatialDirections ψ) ∧
    (∀ ψ, ψ ∈ FormDomain T ↔ SobolevOne spatialDirections ψ)
  fermion : ∀ F a v A V W,
    PlanarSpectralLibrary.PlanarCoefficients a v A V →
    (∃ C : ℝ, ∀ p, |V p| ≤ C) → ContDiff ℝ ∞ W →
    (∃ C : ℝ, ∀ z, |W z| ≤ C) → FermionRealization.Facts F A V W →
    (∀ ψ : FermionRealization.FermionState,
      ψ ∈ F.domain ↔ SobolevTwo pairDirections (ψ : FermionRealization.PairState)) ∧
    (∀ ψ : FermionRealization.FermionState,
      ψ ∈ FormDomain F ↔ SobolevOne pairDirections (ψ : FermionRealization.PairState))

def spectralSum (s t : Set ℝ) : Set ℝ := {E | ∃ p ∈ s, ∃ z ∈ t, p + z = E}

/-- Weyl stability under decaying magnetic/scalar perturbations, and the
essential spectrum of the actual tensor sum of lower-bounded factors. -/
structure StandardWeylLibrary : Prop where
  planar : ∀ P a v U A V β,
    PlanarSpectralLibrary.PlanarCoefficients a v A V →
    (∃ C : ℝ, ∀ p, |V p| ≤ C) → PlanarSpectralLibrary.Facts P a v U A V →
    Tendsto a atTop (𝓝 0) → Tendsto v atTop (𝓝 β) →
    essentialSpectrum P.H = Ici β
  tensor : ∀ T P Z a v U A V Q W,
    PlanarSpectralLibrary.PlanarCoefficients a v A V →
    (∃ C : ℝ, ∀ p, |V p| ≤ C) → AxialRealization.Coefficients Q W →
    PlanarSpectralLibrary.Facts P a v U A V → AxialRealization.Facts Z Q W →
    TensorRealization.Facts T P Z A V W →
    (∀ E ∈ P.spectrum, 0 ≤ E) → (∀ E ∈ Z.spectrum, 0 ≤ E) →
    essentialSpectrum T = spectralSum (essentialSpectrum P.H) Z.spectrum ∪
      spectralSum P.spectrum (essentialSpectrum Z.H)
  constant_partner_no_positive_eigenvalues : ∀ Z U V k,
    AxialRealization.Coefficients U V → AxialRealization.Facts Z U V →
    (∀ z, U z ^ 2 + deriv U z = k) →
    ∀ E, E ≠ 0 → ∀ ψ, ¬ Eigen Z.H E ψ

theorem bounded_planar_domains (library : StandardKatoRellichLibrary)
    (t : ℝ) (ht : 0 < t) (P : PlanarSpectralLibrary.System)
    (hP : PlanarSpectralLibrary.Facts P (Noninteracting.profileA t)
      (RadialEndpoints.regularProfileV t) (Noninteracting.profileU t)
      (Cartesian.boundedVector t) (Cartesian.boundedScalar t)) :
    (∀ ψ, ψ ∈ P.H.domain ↔ SobolevTwo planarDirections ψ) ∧
    (∀ ψ, ψ ∈ FormDomain P.H ↔ SobolevOne planarDirections ψ) :=
  library.planar _ _ _ _ _ _ (PlanarSpectralLibrary.bounded_planar_coefficients t ht)
    (ConstructionData.boundedScalar_bounded t ht) hP

theorem bounded_axial_domains (library : StandardKatoRellichLibrary)
    (c : ℝ) (Z : AxialRealization.System)
    (hZ : AxialRealization.Facts Z (Axial.superpotential c) (Axial.potential c)) :
    (∀ ψ, ψ ∈ Z.H.domain ↔ SobolevTwo axialDirections ψ) ∧
    (∀ ψ, ψ ∈ FormDomain Z.H ↔ SobolevOne axialDirections ψ) :=
  library.axial _ _ _ (AxialRealization.bounded_coefficients c) hZ

theorem bounded_spatial_domains (library : StandardKatoRellichLibrary)
    (t c : ℝ) (ht : 0 < t) (T : TensorRealization.System)
    (hT : FermionRealization.OneBodyRealization T (Cartesian.boundedVector t)
      (Cartesian.boundedScalar t) (Axial.potential c)) :
    (∀ ψ, ψ ∈ T.domain ↔ SobolevTwo spatialDirections ψ) ∧
    (∀ ψ, ψ ∈ FormDomain T ↔ SobolevOne spatialDirections ψ) :=
  library.tensor _ _ _ _ _ _ (PlanarSpectralLibrary.bounded_planar_coefficients t ht)
    (ConstructionData.boundedScalar_bounded t ht) (Axial.potential_smooth c)
    ⟨c ^ 2, Axial.potential_bounded c⟩ hT

theorem bounded_fermion_domains (library : StandardKatoRellichLibrary)
    (t c : ℝ) (ht : 0 < t) (F : FermionRealization.System)
    (hF : FermionRealization.Facts F (Cartesian.boundedVector t)
      (Cartesian.boundedScalar t) (Axial.potential c)) :
    (∀ ψ : FermionRealization.FermionState,
      ψ ∈ F.domain ↔ SobolevTwo pairDirections (ψ : FermionRealization.PairState)) ∧
    (∀ ψ : FermionRealization.FermionState,
      ψ ∈ FormDomain F ↔ SobolevOne pairDirections (ψ : FermionRealization.PairState)) :=
  library.fermion _ _ _ _ _ _ (PlanarSpectralLibrary.bounded_planar_coefficients t ht)
    (ConstructionData.boundedScalar_bounded t ht) (Axial.potential_smooth c)
    ⟨c ^ 2, Axial.potential_bounded c⟩ hF

theorem bounded_planar_essential_spectrum (library : StandardWeylLibrary)
    (t : ℝ) (ht : 0 < t) (P : PlanarSpectralLibrary.System)
    (hP : PlanarSpectralLibrary.Facts P (Noninteracting.profileA t)
      (RadialEndpoints.regularProfileV t) (Noninteracting.profileU t)
      (Cartesian.boundedVector t) (Cartesian.boundedScalar t)) :
    essentialSpectrum P.H = Ici (441 / 4) :=
  library.planar _ _ _ _ _ _ _ (PlanarSpectralLibrary.bounded_planar_coefficients t ht)
    (ConstructionData.boundedScalar_bounded t ht) hP
    (PotentialInfinity.profileA_tendsto_atTop t ht)
    (PotentialInfinity.regularProfileV_tendsto_atTop t ht)

theorem bounded_axial_spectrum (c : ℝ) (hc : 0 < c) (Z : AxialRealization.System)
    (hZ : AxialRealization.Facts Z (Axial.superpotential c) (Axial.potential c)) :
    spectrum Z.H = {0} ∪ Ici (c ^ 2) := by
  have hz := (AxialRealization.bounded_axial_levels c hc Z hZ).2.1
  rw [← hZ.spectrum_identification]
  ext E
  by_cases hE : E = 0
  · subst E
    simp [hz]
  · rw [hZ.nonzero_spectrum E hE,
      hZ.constant_partner (c ^ 2) (fun z => (Axial.factorization c z).2)]
    simp [hE]

theorem bounded_axial_essential_spectrum (c : ℝ) (hc : 0 < c) (Z : AxialRealization.System)
    (hZ : AxialRealization.Facts Z (Axial.superpotential c) (Axial.potential c)) :
    essentialSpectrum Z.H = Ici (c ^ 2) := by
  have hspec := bounded_axial_spectrum c hc Z hZ
  obtain ⟨he, _, hm, hgap⟩ := AxialRealization.bounded_axial_levels c hc Z hZ
  have hsq : 0 < c ^ 2 := sq_pos_of_pos hc
  have hd : DiscreteEigenvalue Z.H 0 := by
    refine ⟨⟨AxialRealization.chiState c hc, he⟩, ?_, c ^ 2, hsq, ?_⟩
    · apply Module.finite_of_finrank_pos
      change 0 < OperatorModel.multiplicity Z.H 0
      rw [← hZ.multiplicity_identification, hm]
      norm_num
    · intro e he' hlt
      rw [← hZ.spectrum_identification] at he'
      rcases hgap e he' with h | h
      · exact h
      · have := le_abs_self e
        simp only [sub_zero] at hlt
        linarith
  ext E
  constructor
  · rintro ⟨hE, hn⟩
    rw [hspec] at hE
    rcases hE with h | h
    · have he : E = 0 := mem_singleton_iff.mp h
      subst E
      exact False.elim (hn hd)
    · exact h
  · intro hE
    refine ⟨by rw [hspec]; exact Or.inr hE, ?_⟩
    rintro ⟨_, _, ε, hε, hi⟩
    have hs : E + ε / 2 ∈ spectrum Z.H := by
      rw [hspec]
      exact Or.inr (by change c ^ 2 ≤ E at hE; change c ^ 2 ≤ E + ε / 2; linarith)
    have heq := hi (E + ε / 2) hs (by
      rw [show E + ε / 2 - E = ε / 2 by ring, abs_of_pos (by positivity)]
      linarith)
    linarith

theorem bounded_axial_only_eigenvalue (library : StandardWeylLibrary)
    (c E : ℝ) (Z : AxialRealization.System)
    (hZ : AxialRealization.Facts Z (Axial.superpotential c) (Axial.potential c))
    (ψ : AxialRealization.State) (hψ : Eigen Z.H E ψ) : E = 0 := by
  by_contra hE
  exact library.constant_partner_no_positive_eigenvalues Z _ _ (c ^ 2)
    (AxialRealization.bounded_coefficients c) hZ
    (fun z => (Axial.factorization c z).2) E hE ψ hψ

theorem spectralSum_halfline (s : Set ℝ) (a : ℝ)
    (h0 : 0 ∈ s) (hn : ∀ e ∈ s, 0 ≤ e) : spectralSum (Ici a) s = Ici a := by
  ext E
  constructor
  · rintro ⟨p, hp, z, hz, rfl⟩
    exact le_add_of_nonneg_right (hn z hz) |>.trans' hp
  · intro hE
    exact ⟨E, hE, 0, h0, add_zero E⟩

theorem spectralSum_comm (s t : Set ℝ) : spectralSum s t = spectralSum t s := by
  ext E
  constructor <;> rintro ⟨p, hp, z, hz, he⟩ <;> exact ⟨z, hz, p, hp, by linarith⟩

theorem bounded_tensor_essential_spectrum (library : StandardWeylLibrary)
    (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (P : PlanarSpectralLibrary.System) (Z : AxialRealization.System)
    (T : TensorRealization.System)
    (hP : PlanarSpectralLibrary.Facts P (Noninteracting.profileA t)
      (RadialEndpoints.regularProfileV t) (Noninteracting.profileU t)
      (Cartesian.boundedVector t) (Cartesian.boundedScalar t))
    (hZ : AxialRealization.Facts Z (Axial.superpotential c) (Axial.potential c))
    (hT : TensorRealization.Facts T P Z (Cartesian.boundedVector t)
      (Cartesian.boundedScalar t) (Axial.potential c))
    (hpnon : ∀ E ∈ P.spectrum, 0 ≤ E) :
    essentialSpectrum T = Ici (min (c ^ 2) (441 / 4)) := by
  have hp0 : 0 ∈ P.spectrum := by
    have he := PlanarSpectralLibrary.bounded_zero_lift_eigen t ht P hP
    intro hr
    obtain ⟨R, _, _, hleft⟩ := hr
    obtain ⟨hψ, hn, heq⟩ := he
    have hh := hleft _ hψ
    rw [heq, zero_smul, sub_zero, map_zero] at hh
    exact hn hh.symm
  have hz0 := (AxialRealization.bounded_axial_levels c hc Z hZ).2.1
  rw [library.tensor T P Z _ _ _ _ _ _ _
    (PlanarSpectralLibrary.bounded_planar_coefficients t ht)
    (ConstructionData.boundedScalar_bounded t ht) (AxialRealization.bounded_coefficients c)
    hP hZ hT hpnon hZ.nonnegative,
    bounded_planar_essential_spectrum library t ht P hP,
    bounded_axial_essential_spectrum c hc Z hZ,
    spectralSum_halfline Z.spectrum _ hz0 hZ.nonnegative,
    spectralSum_comm P.spectrum (Ici (c ^ 2)),
    spectralSum_halfline P.spectrum _ hp0 hpnon]
  ext E
  simp only [mem_union, mem_Ici, min_le_iff]
  tauto

end MagHK.OperatorPreliminaries
