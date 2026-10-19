import MagHK.SpinChart
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Finite multiplicity spaces for monopole angular momentum. The general
isotypic decomposition theorem is separated from the rank-two deduction.
In particular the rank-two common-radial conclusion is proved below. -/
noncomputable section
namespace MagHK.MonopoleMultiplet
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.MonopoleTrial MagHK.SpinChart
open scoped BigOperators

/-- The angular eigenbasis in a charge sector. Its zero block is fixed to
our explicit north-patch doublet when the twice-charge is one. -/
structure AngularBasis (q : ℤ) where
  harmonic : ℕ → ℕ → Angle → ℂ
  lowest_plus : q = 1 → harmonic 0 0 = Yplus
  lowest_minus : q = 1 → harmonic 0 1 = Yminus

/-- The standard finite-multiplicity isotypic decomposition, expressed on
actual L² representatives. This data applies to every finite invariant
subspace, not just one of dimension two. -/
structure FiniteMultiplets (q : ℤ) (Y : AngularBasis q) (K : Submodule ℂ State) where
  count : ℕ
  level : Fin count → ℕ
  radial : Fin count → ℝ → ℂ
  radial_normalized : ∀ a, (∫ r, Complex.normSq (radial a r) ∂radialVolume) = 1
  basis : Module.Basis (Σ a : Fin count, Fin (q.natAbs + 2 * level a + 1)) ℂ K
  representative : ∀ a m, ∀ᵐ x ∂chartMeasure,
    (basis ⟨a, m⟩).val x = radial a x.1 * Y.harmonic (level a) m.val x.2

/-- Peter–Weyl decomposition of monopole harmonics followed by the general
finite multiplicity-space form of Schur's lemma. These are unitary operator
representation facts for every charge and every finite invariant subspace.
The eigenfunction and correlation conclusions of the paper are absent. -/
def StandardIsotypicLibrary : Prop :=
  ∀ q (R : AngularMomentumAction q), ∃ Y : AngularBasis q,
    ∀ K : Submodule ℂ State, FiniteDimensional ℂ K →
      (∀ U ψ, ψ ∈ K → R.one U ψ ∈ K) → Nonempty (FiniteMultiplets q Y K)

/-- The full common-radial conclusion from the dimension formula. -/
theorem common_radial_doublet (Y : AngularBasis 1) (K : Submodule ℂ State)
    (M : FiniteMultiplets 1 Y K) (hdim : Module.finrank ℂ K = 2) :
    ∃ f : ℝ → ℂ, ∃ u v : State,
      (∫ r, Complex.normSq (f r) ∂radialVolume) = 1 ∧
      (∀ᵐ x ∂chartMeasure, u x = f x.1 * Yplus x.2) ∧
      (∀ᵐ x ∂chartMeasure, v x = f x.1 * Yminus x.2) ∧
      K = Submodule.span ℂ {u, v} := by
  have hcard : (∑ a : Fin M.count, (2 * M.level a + 2)) = 2 := by
    have hc := Module.finrank_eq_card_basis M.basis
    rw [hdim] at hc
    have hs : (∑ a : Fin M.count, (2 * M.level a + 2)) =
        ∑ a : Fin M.count, ((1 : ℤ).natAbs + 2 * M.level a + 1) := by
      apply Finset.sum_congr rfl
      intro a _
      norm_num
      omega
    rw [hs]
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hc.symm
  have hbound : 2 * M.count ≤ 2 := by
    calc
      _ = ∑ _a : Fin M.count, 2 := by simp [mul_comm]
      _ ≤ ∑ a : Fin M.count, (2 * M.level a + 2) :=
        Finset.sum_le_sum (fun _ _ => by omega)
      _ = 2 := hcard
  have hcount : M.count = 1 := by
    have hn : M.count ≠ 0 := by
      intro hz
      have he : IsEmpty (Fin M.count) := by rw [hz]; infer_instance
      letI := he
      simp at hcard
    omega
  let a : Fin M.count := ⟨0, by omega⟩
  have ha (b : Fin M.count) : b = a := by
    apply Fin.ext
    have hb := b.isLt
    dsimp [a]
    omega
  have hlevel : M.level a = 0 := by
    have he : (∑ b : Fin M.count, (2 * M.level b + 2)) = 2 * M.level a + 2 := by
      simp_rw [ha]
      simp [hcount]
    rw [he] at hcard
    omega
  have hdim_a : (1 : ℤ).natAbs + 2 * M.level a + 1 = 2 := by simp [hlevel]
  let m₀ : Fin ((1 : ℤ).natAbs + 2 * M.level a + 1) := ⟨0, by omega⟩
  let m₁ : Fin ((1 : ℤ).natAbs + 2 * M.level a + 1) := ⟨1, by omega⟩
  let i₀ : Σ b : Fin M.count, Fin ((1 : ℤ).natAbs + 2 * M.level b + 1) := ⟨a, m₀⟩
  let i₁ : Σ b : Fin M.count, Fin ((1 : ℤ).natAbs + 2 * M.level b + 1) := ⟨a, m₁⟩
  have hi (i : Σ b : Fin M.count, Fin ((1 : ℤ).natAbs + 2 * M.level b + 1)) :
      i = i₀ ∨ i = i₁ := by
    rcases i with ⟨b, m⟩
    have hb := ha b
    subst b
    have hm : m.val = 0 ∨ m.val = 1 := by have hlt := m.isLt; omega
    rcases hm with hm | hm
    · left
      have he : m = m₀ := Fin.ext hm
      exact congrArg (Sigma.mk a) he
    · right
      have he : m = m₁ := Fin.ext hm
      exact congrArg (Sigma.mk a) he
  refine ⟨M.radial a, (M.basis i₀).val, (M.basis i₁).val,
    M.radial_normalized a, ?_, ?_, ?_⟩
  · simpa only [i₀, m₀, hlevel, Y.lowest_plus rfl] using M.representative a m₀
  · simpa only [i₁, m₁, hlevel, Y.lowest_minus rfl] using M.representative a m₁
  · apply le_antisymm
    · intro ψ hψ
      have he := congrArg K.subtype (M.basis.sum_repr (⟨ψ, hψ⟩ : K))
      simp only [map_sum, map_smul, Submodule.subtype_apply] at he
      rw [← he]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      rcases hi i with rfl | rfl <;> simp
    · apply Submodule.span_le.mpr
      intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl
      · exact (M.basis i₀).property
      · exact (M.basis i₁).property

end MagHK.MonopoleMultiplet
