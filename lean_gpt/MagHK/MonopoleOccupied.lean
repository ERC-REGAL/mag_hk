import MagHK.SpinChart
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Recovering the occupied orbital space from a literal Slater determinant.
The proof contracts the actual product-space wavefunction against an orbital.
No exterior-space invariance or rank-two projection assertion is assumed. -/
noncomputable section
namespace MagHK.MonopoleRealization
open MeasureTheory

/-- A literal normalized Slater determinant of two orthonormal L² sections. -/
def IsSlater (ψ : FermionState) : Prop :=
  ∃ f g : State, Orthonormal ℂ ![f, g] ∧
    ∀ᵐ p ∂pairMeasure, (ψ : PairState) p = determinant f g p

end MagHK.MonopoleRealization

namespace MagHK.MonopoleOccupied
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.SpinChart
open scoped ComplexConjugate

theorem inner_integral (f g : State) :
    inner ℂ f g = ∫ x, conj (f x) * g x ∂chartMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp [mul_comm])

theorem pairing_integrable (f g : State) :
    Integrable (fun x => conj (f x) * g x) chartMeasure := by
  have h := L2.integrable_inner (𝕜 := ℂ) f g
  apply h.congr
  exact ae_of_all _ (fun x => by dsimp only; simp [mul_comm])

/-- Literal partial inner product of an arbitrary L² orbital with a Slater
determinant. Each scalar pairing is integrable by the L² Cauchy–Schwarz theorem. -/
theorem determinant_contraction (f g h : State) (x : Chart) :
    (∫ y, conj (h y) * determinant f g (x, y) ∂chartMeasure) =
      MagHK.Slater.scale * (f x * inner ℂ h g - g x * inner ℂ h f) := by
  have he (y : Chart) : conj (h y) * determinant f g (x, y) =
      MagHK.Slater.scale * (f x * (conj (h y) * g y) - g x * (conj (h y) * f y)) := by
    unfold determinant MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub ((pairing_integrable h g).const_mul _)
    ((pairing_integrable h f).const_mul _), integral_const_mul, integral_const_mul,
      ← inner_integral, ← inner_integral]

private theorem scale_ne_zero : MagHK.Slater.scale ≠ 0 := by
  unfold MagHK.Slater.scale
  apply inv_ne_zero
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))

theorem first_mem_of_determinant_eq (f g u v : State)
    (hvv : inner ℂ v v = 1) (hvu : inner ℂ v u = 0)
    (he : determinant u v =ᵐ[pairMeasure] determinant f g) :
    u ∈ Submodule.span ℂ ({f, g} : Set State) := by
  have hxy := Measure.ae_ae_of_ae_prod he
  have hu : u = (inner ℂ v g) • f + (-inner ℂ v f) • g := by
    apply Lp.ext
    filter_upwards [hxy, Lp.coeFn_add ((inner ℂ v g) • f) ((-inner ℂ v f) • g),
      Lp.coeFn_smul (inner ℂ v g) f, Lp.coeFn_smul (-inner ℂ v f) g] with x hx hadd hf hg
    have hi : (∫ y, conj (v y) * determinant u v (x, y) ∂chartMeasure) =
        ∫ y, conj (v y) * determinant f g (x, y) ∂chartMeasure := by
      apply integral_congr_ae
      filter_upwards [hx] with y hy
      rw [hy]
    rw [determinant_contraction, determinant_contraction, hvv, hvu,
      mul_one, mul_zero, sub_zero] at hi
    have hp := mul_left_cancel₀ scale_ne_zero hi
    rw [hadd]
    dsimp only [Pi.add_apply]
    rw [hf, hg]
    change u x = (inner ℂ v g) * f x + (-inner ℂ v f) * g x
    rw [hp]
    ring
  exact Submodule.mem_span_pair.mpr ⟨inner ℂ v g, -inner ℂ v f, hu.symm⟩

theorem determinant_swap (f g : Chart → ℂ) (p : Chart × Chart) :
    determinant g f p = -determinant f g p := by
  unfold determinant MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
  ring

theorem occupied_of_determinant_eq (f g u v : State)
    (huv : Orthonormal ℂ ![u, v])
    (he : determinant u v =ᵐ[pairMeasure] determinant f g) :
    u ∈ Submodule.span ℂ ({f, g} : Set State) ∧
      v ∈ Submodule.span ℂ ({f, g} : Set State) := by
  have hn := orthonormal_iff_ite.mp huv
  constructor
  · apply first_mem_of_determinant_eq f g u v
    · simpa using hn 1 1
    · simpa using hn 1 0
    · exact he
  · have hs : determinant v u =ᵐ[pairMeasure] determinant g f := by
      filter_upwards [he] with p hp
      rw [determinant_swap u v p, determinant_swap f g p, hp]
    have hm := first_mem_of_determinant_eq g f v u
      (by simpa using hn 0 0) (by simpa using hn 0 1) hs
    simpa only [Set.pair_comm] using hm

def oneIsometry {q : ℤ} (R : AngularMomentumAction q) (U : MagHK.Spin.Group) :
    State →ₗᵢ[ℂ] State where
  toLinearMap := R.one U
  norm_map' := R.one_norm U

theorem transformed_orthonormal {q : ℤ} (R : AngularMomentumAction q) (U : MagHK.Spin.Group)
    (f g : State) (hfg : Orthonormal ℂ ![f, g]) :
    Orthonormal ℂ ![R.one U f, R.one U g] := by
  have h := hfg.comp_linearIsometry (oneIsometry R U)
  have he : (oneIsometry R U) ∘ (![f, g] : Fin 2 → State) = ![R.one U f, R.one U g] := by
    funext i
    fin_cases i <;> rfl
  rwa [he] at h

theorem invariant_determinant {q : ℤ} (R : AngularMomentumAction q)
    (ψ : FermionState) (f g : State)
    (hrep : ∀ᵐ p ∂pairMeasure, (ψ : PairState) p = determinant f g p)
    (hs : ∀ U, R.pair U ψ = ψ) (U : MagHK.Spin.Group) :
    determinant (R.one U f) (R.one U g) =ᵐ[pairMeasure] determinant f g := by
  have hmove := (R.chart_measure U).prod (R.chart_measure U)
  have hrep' := hmove.quasiMeasurePreserving.ae hrep
  have hf := R.one_formula U f
  have hg := R.one_formula U g
  filter_upwards [hrep, hrep', R.pair_formula U ψ,
    Measure.quasiMeasurePreserving_fst.ae hf, Measure.quasiMeasurePreserving_snd.ae hf,
    Measure.quasiMeasurePreserving_fst.ae hg, Measure.quasiMeasurePreserving_snd.ae hg] with
      p hp hp' hpair hf1 hf2 hg1 hg2
  calc
    _ = determinant (actionWave q U f) (actionWave q U g) p := by
      unfold determinant MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
      rw [hf1, hf2, hg1, hg2]
    _ = actionPairWave q U (determinant f g) p := (congrFun (action_determinant q U f g) p).symm
    _ = actionPairWave q U (ψ : PairState) p := by
      unfold actionPairWave
      change (ψ : PairState) (movedChart U p.1, movedChart U p.2) =
        determinant f g (movedChart U p.1, movedChart U p.2) at hp'
      rw [hp']
    _ = ((R.pair U ψ : FermionState) : PairState) p := hpair.symm
    _ = (ψ : PairState) p := by rw [hs U]
    _ = _ := hp

theorem occupied_dimension (f g : State) (hfg : Orthonormal ℂ ![f, g]) :
    FiniteDimensional ℂ (Submodule.span ℂ ({f, g} : Set State)) ∧
      Module.finrank ℂ (Submodule.span ℂ ({f, g} : Set State)) = 2 := by
  have hr : Set.range (![f, g] : Fin 2 → State) = {f, g} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  refine ⟨FiniteDimensional.span_of_finite ℂ (Set.toFinite _), ?_⟩
  rw [← hr, finrank_span_eq_card hfg.linearIndependent]
  rfl

/-- An invariant normalized Slater determinant has an actual two-dimensional
invariant occupied orbital space. This follows from literal L² contractions. -/
theorem occupied_invariant {q : ℤ} (R : AngularMomentumAction q)
    (ψ : FermionState) (f g : State) (hfg : Orthonormal ℂ ![f, g])
    (hrep : ∀ᵐ p ∂pairMeasure, (ψ : PairState) p = determinant f g p)
    (hs : ∀ U, R.pair U ψ = ψ) :
    FiniteDimensional ℂ (Submodule.span ℂ ({f, g} : Set State)) ∧
      Module.finrank ℂ (Submodule.span ℂ ({f, g} : Set State)) = 2 ∧
      ∀ U ξ, ξ ∈ Submodule.span ℂ ({f, g} : Set State) →
        R.one U ξ ∈ Submodule.span ℂ ({f, g} : Set State) := by
  obtain ⟨hfinite, hdim⟩ := occupied_dimension f g hfg
  refine ⟨hfinite, hdim, ?_⟩
  intro U ξ hξ
  obtain ⟨hf, hg⟩ := occupied_of_determinant_eq f g (R.one U f) (R.one U g)
    (transformed_orthonormal R U f g hfg) (invariant_determinant R ψ f g hrep hs U)
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hξ
  rw [map_add, map_smul, map_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg)

theorem determinant_basis_change (a b c d : ℂ) (u v : Chart → ℂ) (p : Chart × Chart) :
    determinant (fun x => a * u x + b * v x) (fun x => c * u x + d * v x) p =
      (a * d - b * c) * determinant u v p := by
  unfold determinant MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
  ring

/-- Equality of occupied subspaces gives the actual determinant a single
constant factor after a basis change. This is an almost-everywhere function
identity, not a statement about an abstract exterior-algebra label. -/
theorem determinant_span_change (f g u v : State)
    (hf : f ∈ Submodule.span ℂ ({u, v} : Set State))
    (hg : g ∈ Submodule.span ℂ ({u, v} : Set State)) :
    ∃ c : ℂ, determinant f g =ᵐ[pairMeasure] fun p => c * determinant u v p := by
  obtain ⟨a, b, hfab⟩ := Submodule.mem_span_pair.mp hf
  obtain ⟨c, d, hgcd⟩ := Submodule.mem_span_pair.mp hg
  have hf' : ∀ᵐ x ∂chartMeasure, f x = a * u x + b * v x := by
    rw [← hfab]
    filter_upwards [Lp.coeFn_add (a • u) (b • v), Lp.coeFn_smul a u,
      Lp.coeFn_smul b v] with x ha hu hv
    rw [ha]
    dsimp only [Pi.add_apply]
    rw [hu, hv]
    rfl
  have hg' : ∀ᵐ x ∂chartMeasure, g x = c * u x + d * v x := by
    rw [← hgcd]
    filter_upwards [Lp.coeFn_add (c • u) (d • v), Lp.coeFn_smul c u,
      Lp.coeFn_smul d v] with x ha hu hv
    rw [ha]
    dsimp only [Pi.add_apply]
    rw [hu, hv]
    rfl
  refine ⟨a * d - b * c, ?_⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hf',
    Measure.quasiMeasurePreserving_snd.ae hf', Measure.quasiMeasurePreserving_fst.ae hg',
    Measure.quasiMeasurePreserving_snd.ae hg'] with p hf1 hf2 hg1 hg2
  unfold determinant MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
  rw [hf1, hf2, hg1, hg2]
  ring

end MagHK.MonopoleOccupied
