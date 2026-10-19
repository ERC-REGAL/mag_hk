import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Finiteness

/-! The dual of an L1–Lp intersection. The intersection is the actual
diagonal subspace of L1×Lp with its inherited norm. Hahn–Banach is proved
in mathlib; only the general finite-exponent Lp dual representation is
external. No density/current space is an input to that representation. -/
noncomputable section
namespace MagHK.BanachDuality
open MeasureTheory Set
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Standard Radon–Nikodym/Lp dual representation for all finite p≥1. -/
def StandardLpDualityLibrary : Prop :=
  SigmaFinite μ → ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    p < ∞ → ∀ L : Lp ℝ p μ →L[ℝ] ℝ,
      ∃ g : Lp ℝ q μ, ∀ f : Lp ℝ p μ, L f = ∫ x, g x * f x ∂μ

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def diagonal : Submodule ℝ (Lp ℝ 1 μ × Lp ℝ p μ) where
  carrier := {u | (u.1 : X → ℝ) =ᵐ[μ] u.2}
  zero_mem' := (Lp.coeFn_zero ℝ 1 μ).trans (Lp.coeFn_zero ℝ p μ).symm
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu, hv, Lp.coeFn_add u.1 v.1, Lp.coeFn_add u.2 v.2] with x hu hv h1 h2
    change (u.1 + v.1) x = (u.2 + v.2) x
    rw [h1, h2]
    exact congrArg₂ (· + ·) hu hv
  smul_mem' := by
    intro c u hu
    filter_upwards [hu, Lp.coeFn_smul c u.1, Lp.coeFn_smul c u.2] with x hu h1 h2
    change (c • u.1) x = (c • u.2) x
    rw [h1, h2]
    exact congrArg (fun r : ℝ => c * r) hu

abbrev Intersection := diagonal μ p

def Represents (v : X → ℝ) (L : Intersection μ p →L[ℝ] ℝ) : Prop :=
  ∀ u : Intersection μ p, L u = ∫ x, v x * u.val.1 x ∂μ

def SumSpace (q : ℝ≥0∞) (v : X → ℝ) : Prop :=
  ∃ a b : X → ℝ, MemLp a q μ ∧ MemLp b ∞ μ ∧ v = a + b

variable {μ p}

omit [Fact (1 ≤ p)] in
theorem pairing_integrable {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (a : Lp ℝ q μ) (b : Lp ℝ ∞ μ) (u : Intersection μ p) :
    Integrable (fun x => (a x + b x) * u.val.1 x) μ := by
  have ha : Integrable (fun x => a x * u.val.2 x) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp u.val.2).mul' (Lp.memLp a))
  have hb : Integrable (fun x => b x * u.val.1 x) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp u.val.1).mul' (Lp.memLp b))
  apply (ha.add hb).congr
  filter_upwards [u.property] with x hx
  change a x * u.val.2 x + b x * u.val.1 x = (a x + b x) * u.val.1 x
  rw [← hx]
  ring

theorem functional_representation [SigmaFinite μ] (duality : StandardLpDualityLibrary μ)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] (hp : p < ∞)
    (L : Intersection μ p →L[ℝ] ℝ) :
    ∃ a : Lp ℝ q μ, ∃ b : Lp ℝ ∞ μ, Represents μ p (fun x => a x + b x) L := by
  obtain ⟨T, hT, _⟩ := exists_extension_norm_eq (diagonal μ p) L
  let T₁ := T.comp (ContinuousLinearMap.inl ℝ (Lp ℝ 1 μ) (Lp ℝ p μ))
  let T₂ := T.comp (ContinuousLinearMap.inr ℝ (Lp ℝ 1 μ) (Lp ℝ p μ))
  obtain ⟨b, hb⟩ := duality inferInstance 1 ∞ (by norm_num) T₁
  obtain ⟨a, ha⟩ := duality inferInstance p q hp T₂
  refine ⟨a, b, ?_⟩
  intro u
  have hsplit : L u = T₁ u.val.1 + T₂ u.val.2 := by
    rw [← hT u]
    change T u.val = T (u.val.1, 0) + T (0, u.val.2)
    rw [← map_add]
    congr 1
    simp
  rw [hsplit, hb, ha]
  have hia : Integrable (fun x => a x * u.val.2 x) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp u.val.2).mul' (Lp.memLp a))
  have hib : Integrable (fun x => b x * u.val.1 x) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp u.val.1).mul' (Lp.memLp b))
  rw [← integral_add hib hia]
  apply integral_congr_ae
  filter_upwards [u.property] with x hx
  rw [← hx]
  ring

def integralFunctional {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (a : Lp ℝ q μ) (b : Lp ℝ ∞ μ) : Intersection μ p →L[ℝ] ℝ :=
  (((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p a).comp
    ((ContinuousLinearMap.snd ℝ (Lp ℝ 1 μ) (Lp ℝ p μ)).comp (diagonal μ p).subtypeL)) +
  (((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1 b).comp
    ((ContinuousLinearMap.fst ℝ (Lp ℝ 1 μ) (Lp ℝ p μ)).comp (diagonal μ p).subtypeL))

theorem integralFunctional_represents {q : ℝ≥0∞}
    [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (a : Lp ℝ q μ) (b : Lp ℝ ∞ μ) :
    Represents μ p (fun x => a x + b x) (integralFunctional a b) := by
  intro u
  change (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p a u.val.2 +
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1 b u.val.1 = _
  rw [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.lpPairing_eq_integral]
  simp only [ContinuousLinearMap.mul_apply']
  have ha : Integrable (fun x => a x * u.val.2 x) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp u.val.2).mul' (Lp.memLp a))
  have hb : Integrable (fun x => b x * u.val.1 x) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp u.val.1).mul' (Lp.memLp b))
  rw [← integral_add ha hb]
  apply integral_congr_ae
  filter_upwards [u.property] with x hx
  rw [← hx]
  ring

theorem represents_congr {v w : X → ℝ} {L : Intersection μ p →L[ℝ] ℝ}
    (h : Represents μ p v L) (hv : v =ᵐ[μ] w) : Represents μ p w L := by
  intro u
  rw [h u]
  apply integral_congr_ae
  exact hv.mono (fun _ hx => congrArg (fun r : ℝ => r * _) hx)

theorem sum_space_functional {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (v : X → ℝ) (hv : SumSpace μ q v) :
    ∃ L : Intersection μ p →L[ℝ] ℝ, Represents μ p v L := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hv
  refine ⟨integralFunctional (ha.toLp a) (hb.toLp b), ?_⟩
  apply represents_congr (integralFunctional_represents (ha.toLp a) (hb.toLp b))
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
  exact congrArg₂ (· + ·) hx hy

def indicator (s : Set X) (hs : MeasurableSet s) (hμ : μ s < ∞) : Intersection μ p :=
  ⟨(indicatorConstLp 1 hs hμ.ne (1 : ℝ), indicatorConstLp p hs hμ.ne (1 : ℝ)),
    (indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμ.ne) (c := (1 : ℝ))).trans
      (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμ.ne) (c := (1 : ℝ))).symm⟩

theorem represents_indicator {v : X → ℝ} {L : Intersection μ p →L[ℝ] ℝ}
    (h : Represents μ p v L) (s : Set X) (hs : MeasurableSet s) (hμ : μ s < ∞) :
    L (indicator s hs hμ) = ∫ x in s, v x ∂μ := by
  rw [h, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμ.ne) (c := (1 : ℝ))] with x hx
  change v x * indicatorConstLp 1 hs hμ.ne 1 x = s.indicator v x
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem sum_space_integrableOn {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {v : X → ℝ} (hv : SumSpace μ q v) (s : Set X) (hμ : μ s < ∞) : IntegrableOn v s μ := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hv
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμ⟩
  exact (MemLp.integrable (Fact.out : 1 ≤ q) (ha.restrict s)).add
    (MemLp.integrable le_top (hb.restrict s))

theorem potential_unique [SigmaFinite μ] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {v w : X → ℝ} (hv : SumSpace μ q v) (hw : SumSpace μ q w)
    {L : Intersection μ p →L[ℝ] ℝ} (hL : Represents μ p v L) (hL' : Represents μ p w L) :
    v =ᵐ[μ] w := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hs => sum_space_integrableOn hv s hs)
    (fun s _ hs => sum_space_integrableOn hw s hs)
  intro s hs hμ
  exact (represents_indicator hL s hs hμ).symm.trans (represents_indicator hL' s hs hμ)

theorem dual_representation [SigmaFinite μ] (duality : StandardLpDualityLibrary μ)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] (hp : p < ∞) :
    (∀ L : Intersection μ p →L[ℝ] ℝ, ∃ v : X → ℝ, SumSpace μ q v ∧ Represents μ p v L) ∧
    (∀ v : X → ℝ, SumSpace μ q v → ∃! L : Intersection μ p →L[ℝ] ℝ, Represents μ p v L) := by
  constructor
  · intro L
    obtain ⟨a, b, h⟩ := functional_representation (q := q) duality hp L
    exact ⟨fun x => a x + b x, ⟨a, b, Lp.memLp a, Lp.memLp b, rfl⟩, h⟩
  · intro v hv
    obtain ⟨L, hL⟩ := sum_space_functional (p := p) v hv
    refine ⟨L, hL, ?_⟩
    intro T hT
    apply ContinuousLinearMap.ext
    intro u
    exact (hT u).trans (hL u).symm

/-- Finite Cartesian products introduce no additional duality premise. -/
theorem finite_product_representation [SigmaFinite μ]
    (duality : StandardLpDualityLibrary μ)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] (hp : p < ∞)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → Intersection μ p) →L[ℝ] ℝ) :
    ∃ A : ι → X → ℝ, (∀ i, SumSpace μ q (A i)) ∧
      ∀ u, L u = ∑ i, ∫ x, A i x * (u i).val.1 x ∂μ := by
  have h : ∀ i, ∃ v : X → ℝ, SumSpace μ q v ∧
      Represents μ p v (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => Intersection μ p) i)) := by
    intro i
    exact (dual_representation duality hp).1 _
  choose A hA hrep using h
  refine ⟨A, hA, ?_⟩
  intro u
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => Intersection μ p) L u]
  exact Finset.sum_congr rfl (fun i _ => hrep i (u i))

theorem finite_product_functional {q : ℝ≥0∞} [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → X → ℝ) (hA : ∀ i, SumSpace μ q (A i)) :
    ∃! L : (ι → Intersection μ p) →L[ℝ] ℝ,
      ∀ u, L u = ∑ i, ∫ x, A i x * (u i).val.1 x ∂μ := by
  have h : ∀ i, ∃ L : Intersection μ p →L[ℝ] ℝ, Represents μ p (A i) L :=
    fun i => sum_space_functional (A i) (hA i)
  choose L hL using h
  let T : (ι → Intersection μ p) →L[ℝ] ℝ :=
    ∑ i, (L i).comp (ContinuousLinearMap.proj i)
  have hT : ∀ u, T u = ∑ i, ∫ x, A i x * (u i).val.1 x ∂μ := by
    intro u
    simp only [T, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    exact Finset.sum_congr rfl (fun i _ => hL i (u i))
  refine ⟨T, hT, ?_⟩
  intro S hS
  apply ContinuousLinearMap.ext
  intro u
  exact (hS u).trans (hT u).symm

theorem finite_product_potential_unique [SigmaFinite μ]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ι → X → ℝ) (hA : ∀ i, SumSpace μ q (A i))
    (hB : ∀ i, SumSpace μ q (B i))
    (L : (ι → Intersection μ p) →L[ℝ] ℝ)
    (hLA : ∀ u, L u = ∑ i, ∫ x, A i x * (u i).val.1 x ∂μ)
    (hLB : ∀ u, L u = ∑ i, ∫ x, B i x * (u i).val.1 x ∂μ) :
    ∀ i, A i =ᵐ[μ] B i := by
  have ha : ∀ i, ∃ T : Intersection μ p →L[ℝ] ℝ, Represents μ p (A i) T :=
    fun i => sum_space_functional (A i) (hA i)
  have hb : ∀ i, ∃ T : Intersection μ p →L[ℝ] ℝ, Represents μ p (B i) T :=
    fun i => sum_space_functional (B i) (hB i)
  choose TA hTA using ha
  choose TB hTB using hb
  have hsumA : ∀ u, L u = ∑ i, TA i (u i) := by
    intro u
    rw [hLA u]
    exact Finset.sum_congr rfl (fun i _ => (hTA i (u i)).symm)
  have hsumB : ∀ u, L u = ∑ i, TB i (u i) := by
    intro u
    rw [hLB u]
    exact Finset.sum_congr rfl (fun i _ => (hTB i (u i)).symm)
  intro i
  have he : TA i = TB i := by
    apply ContinuousLinearMap.ext
    intro u
    have h := (hsumA (Pi.single i u)).symm.trans (hsumB (Pi.single i u))
    simpa [Pi.single_apply, apply_ite] using h
  apply potential_unique (hA i) (hB i) (hTA i)
  rw [he]
  exact hTB i

private instance three_ge_one : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩
private instance three_half_ge_one : Fact (1 ≤ (3 / 2 : ℝ≥0∞)) := ⟨by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]⟩
private instance three_conjugate_half : ENNReal.HolderConjugate 3 (3 / 2) := ⟨by
  have hd : (3 / 2 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩

/-- The scalar potential space is exactly the continuous dual of L1∩L3,
with representatives unique modulo almost-everywhere equality. -/
theorem density_dual [SigmaFinite μ] (duality : StandardLpDualityLibrary μ) :
    (∀ L : Intersection μ 3 →L[ℝ] ℝ,
      ∃ v : X → ℝ, SumSpace μ (3 / 2) v ∧ Represents μ 3 v L) ∧
    (∀ v : X → ℝ, SumSpace μ (3 / 2) v →
      ∃! L : Intersection μ 3 →L[ℝ] ℝ, Represents μ 3 v L) :=
  dual_representation duality (by norm_num)

/-- The dual exponent for each component of L1∩L^(3/2) is three. -/
theorem current_component_dual [SigmaFinite μ] (duality : StandardLpDualityLibrary μ) :
    (∀ L : Intersection μ (3 / 2) →L[ℝ] ℝ,
      ∃ A : X → ℝ, SumSpace μ 3 A ∧ Represents μ (3 / 2) A L) ∧
    (∀ A : X → ℝ, SumSpace μ 3 A →
      ∃! L : Intersection μ (3 / 2) →L[ℝ] ℝ, Represents μ (3 / 2) A L) :=
  dual_representation duality (by finiteness)

/-- Every continuous functional on the actual three-component current
space has the literal integral dot-product representation. -/
theorem current_vector_dual [SigmaFinite μ] (duality : StandardLpDualityLibrary μ)
    (L : (Fin 3 → Intersection μ (3 / 2)) →L[ℝ] ℝ) :
    ∃ A : Fin 3 → X → ℝ, (∀ i, SumSpace μ 3 (A i)) ∧
      ∀ u, L u = ∑ i, ∫ x, A i x * (u i).val.1 x ∂μ :=
  finite_product_representation duality (by finiteness) L

theorem current_vector_functional
    (A : Fin 3 → X → ℝ) (hA : ∀ i, SumSpace μ 3 (A i)) :
    ∃! L : (Fin 3 → Intersection μ (3 / 2)) →L[ℝ] ℝ,
      ∀ u, L u = ∑ i, ∫ x, A i x * (u i).val.1 x ∂μ :=
  finite_product_functional A hA

theorem current_vector_potential_unique [SigmaFinite μ]
    (A B : Fin 3 → X → ℝ) (hA : ∀ i, SumSpace μ 3 (A i))
    (hB : ∀ i, SumSpace μ 3 (B i))
    (L : (Fin 3 → Intersection μ (3 / 2)) →L[ℝ] ℝ)
    (hLA : ∀ u, L u = ∑ i, ∫ x, A i x * (u i).val.1 x ∂μ)
    (hLB : ∀ u, L u = ∑ i, ∫ x, B i x * (u i).val.1 x ∂μ) :
    ∀ i, A i =ᵐ[μ] B i :=
  finite_product_potential_unique A B hA hB L hLA hLB

end MagHK.BanachDuality
