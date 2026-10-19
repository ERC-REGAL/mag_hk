import MagHK.FunctionSpaces
import MagHK.BanachDuality
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.FinCases

/-! Finite-dimensional identification of the vector-valued and componentwise
potential sum spaces, for their literal Cartesian representatives. -/
noncomputable section
namespace MagHK.PotentialSpaceIdentification
open MeasureTheory MagHK.FunctionSpaces
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

theorem dual_sumSpace_iff (f : X → ℝ) :
    MagHK.BanachDuality.SumSpace μ p f ↔ SumSpace p f μ := Iff.rfl

/-- Raw L1 and Lp representatives give exactly the diagonal elements used
in the continuous-dual theorem. -/
theorem intersection_representative_iff (f : X → ℝ) :
    FunctionSpaces.Intersection p f μ ↔
      ∃ u : MagHK.BanachDuality.Intersection μ p, (u.val.1 : X → ℝ) =ᵐ[μ] f := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨(h₁.toLp f, h₂.toLp f), ?_⟩, h₁.coeFn_toLp⟩
    exact h₁.coeFn_toLp.trans h₂.coeFn_toLp.symm
  · rintro ⟨u, hu⟩
    have hp : (u.val.1 : X → ℝ) =ᵐ[μ] u.val.2 := u.property
    exact ⟨(Lp.memLp u.val.1).ae_eq hu,
      (Lp.memLp u.val.2).ae_eq (hp.symm.trans hu)⟩

theorem sumSpace_pi_iff {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : X → ∀ i, E i) :
    SumSpace p f μ ↔ ∀ i, SumSpace p (fun x => f x i) μ := by
  constructor
  · rintro ⟨a, b, ha, hb, he⟩ i
    refine ⟨fun x => a x i, fun x => b x i, ha.eval i, hb.eval i, ?_⟩
    ext x
    exact congrFun (congrFun he x) i
  · intro h
    choose a b ha hb he using h
    refine ⟨fun x i => a i x, fun x i => b i x, MemLp.of_eval ha, MemLp.of_eval hb, ?_⟩
    ext x i
    exact congrFun (he i) x

theorem sumSpace_prod_iff {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (f : X → E × F) :
    SumSpace p f μ ↔ SumSpace p (fun x => (f x).1) μ ∧
      SumSpace p (fun x => (f x).2) μ := by
  constructor
  · rintro ⟨a, b, ha, hb, he⟩
    constructor
    · refine ⟨fun x => (a x).1, fun x => (b x).1, ha.fst, hb.fst, ?_⟩
      ext x
      exact congrArg Prod.fst (congrFun he x)
    · refine ⟨fun x => (a x).2, fun x => (b x).2, ha.snd, hb.snd, ?_⟩
      ext x
      exact congrArg Prod.snd (congrFun he x)
  · rintro ⟨⟨a, b, ha, hb, he⟩, ⟨c, d, hc, hd, hf⟩⟩
    refine ⟨fun x => (a x, c x), fun x => (b x, d x),
      MemLp.of_fst_snd ⟨ha, hc⟩, MemLp.of_fst_snd ⟨hb, hd⟩, ?_⟩
    ext x
    exacts [congrFun he x, congrFun hf x]

abbrev Space := MagHK.ConstructionData.Space

def component (A : Space → Space) (i : Fin 3) (x : Space) : ℝ :=
  ![(A x).1.1, (A x).1.2, (A x).2] i

@[simp] theorem component_zero (A : Space → Space) :
    component A 0 = fun x => (A x).1.1 := rfl
@[simp] theorem component_one (A : Space → Space) :
    component A 1 = fun x => (A x).1.2 := rfl
@[simp] theorem component_two (A : Space → Space) :
    component A 2 = fun x => (A x).2 := rfl

theorem vector_sum_iff (A : Space → Space) :
    MagHK.PotentialSpaces.VectorSumSpace A ↔ SumSpace 3 A volume := by
  constructor
  · rintro ⟨a, b, ha, hb, he⟩
    exact ⟨a, b, ha, hb, funext he⟩
  · rintro ⟨a, b, ha, hb, he⟩
    exact ⟨a, b, ha, hb, fun x => congrFun he x⟩

theorem vector_sum_iff_triple (A : Space → Space) :
    MagHK.PotentialSpaces.VectorSumSpace A ↔
      SumSpace 3 (fun x => (A x).1.1) volume ∧
      SumSpace 3 (fun x => (A x).1.2) volume ∧
      SumSpace 3 (fun x => (A x).2) volume := by
  rw [vector_sum_iff, sumSpace_prod_iff, sumSpace_prod_iff, and_assoc]

theorem vector_sum_iff_components (A : Space → Space) :
    MagHK.PotentialSpaces.VectorSumSpace A ↔
      ∀ i, SumSpace 3 (component A i) volume := by
  rw [vector_sum_iff_triple]
  constructor
  · rintro ⟨h₀, h₁, h₂⟩ i
    fin_cases i
    · change SumSpace 3 (fun x => (A x).1.1) volume
      exact h₀
    · change SumSpace 3 (fun x => (A x).1.2) volume
      exact h₁
    · change SumSpace 3 (fun x => (A x).2) volume
      exact h₂
  · intro h
    exact ⟨by simpa only [component_zero] using h 0,
      by simpa only [component_one] using h 1, by simpa only [component_two] using h 2⟩

theorem vector_sum_iff_dual_components (A : Space → Space) :
    MagHK.PotentialSpaces.VectorSumSpace A ↔
      ∀ i, MagHK.BanachDuality.SumSpace volume 3 (component A i) := by
  simp_rw [dual_sumSpace_iff]
  exact vector_sum_iff_components A

theorem componentwise_euclidean_square (A : Space → Space)
    (hA : ∀ i, SumSpace 3 (component A i) volume) :
    MagHK.PotentialSpaces.ScalarSumSpace
      (fun x => (A x).1.1 ^ 2 + (A x).1.2 ^ 2 + (A x).2 ^ 2) :=
  MagHK.FunctionSpaces.vector_euclidean_square A ((vector_sum_iff_components A).mpr hA)

end MagHK.PotentialSpaceIdentification
