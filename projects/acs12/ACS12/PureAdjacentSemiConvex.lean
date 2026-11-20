import ACS12.PeanoWeightedMesh
import ACS12.PeanoMeshBudget

/-! Exact whole A/B semiconvexity obtained from the finite Peano sums. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped BigOperators Topology

private theorem weightedFinitePeano_sum {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc 0 1)) (N : ℕ) (p : ℝ) :
    weightedFinitePeano a w N p =
      a * ∑ j ∈ Finset.range N, ∫ t in (0 : ℝ)..1, w t * peanoPower p (a + t + j * a) := by
  have hI (j : ℕ) : IntervalIntegrable
      (fun t => w t * peanoPower p (a + t + (j : ℝ) * a)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply hw.mul
    unfold peanoPower
    apply continuousOn_const.mul
    have hC : ContinuousOn (fun t : ℝ => a + t + (j : ℝ) * a) (Icc 0 1) := by fun_prop
    apply hC.rpow_const
    intro t ht
    exact Or.inl (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ha ht.1)
      (mul_nonneg (Nat.cast_nonneg j) ha.le)).ne'
  unfold weightedFinitePeano finitePeanoMesh
  have hE (t : ℝ) : w t * (a * ∑ j ∈ Finset.range N,
      peanoPower p (a + t + j * a)) =
      a * ∑ j ∈ Finset.range N, w t * peanoPower p (a + t + j * a) := by
    rw [mul_left_comm (w t) a, Finset.mul_sum (s := Finset.range N)]
  simp_rw [hE, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum (fun j _ => hI j)]

private theorem weightedFinitePeano_A {a : ℝ} (ha : 0 < a) {p : ℝ} (hp : 0 < p) (N : ℕ) :
    weightedFinitePeano a (fun t => t) N p =
      a * ∑ j ∈ Finset.range N, purePeanoA p 1 (a + j * a) := by
  rw [weightedFinitePeano_sum (w := fun t => t) ha continuousOn_id N p]
  apply congrArg (a * ·)
  apply Finset.sum_congr rfl
  intro j _
  have hx : 0 < a + j * a := add_pos_of_pos_of_nonneg ha (mul_nonneg (Nat.cast_nonneg j) ha.le)
  rw [purePeanoA_integral hp zero_lt_one hx, ← intervalIntegral.integral_const_mul]
  apply congrArg (fun f : ℝ → ℝ => ∫ t in (0 : ℝ)..1, f t)
  funext t
  rw [peanoPower, show a + t + (j : ℝ) * a = (a + j * a) + t by ring]
  ring

private theorem weightedFinitePeano_B {a : ℝ} (ha : 0 < a) {p : ℝ} (hp : 0 < p) (N : ℕ) :
    weightedFinitePeano a (fun t => 1 - t) N p =
      a * ∑ j ∈ Finset.range N, purePeanoB p 1 (a + j * a) := by
  rw [weightedFinitePeano_sum (w := fun t => 1 - t) ha (continuousOn_const.sub continuousOn_id) N p]
  apply congrArg (a * ·)
  apply Finset.sum_congr rfl
  intro j _
  have hx : 0 < a + j * a := add_pos_of_pos_of_nonneg ha (mul_nonneg (Nat.cast_nonneg j) ha.le)
  rw [purePeanoB_integral hp zero_lt_one hx, ← intervalIntegral.integral_const_mul]
  apply congrArg (fun f : ℝ → ℝ => ∫ t in (0 : ℝ)..1, f t)
  funext t
  rw [peanoPower, show a + t + (j : ℝ) * a = (a + j * a) + t by ring]
  ring

private theorem pureA_samples_summable {p τ : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hτ : 0 < τ) :
    Summable (fun j : ℕ => purePeanoA p 1 (τ + j * τ)) := by
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨_, _, hB⟩ := lawPeanoDensity_quadratic_bound hp hp₂ zero_lt_one hθ zero_lt_one .a
  have hM := lawPeanoDensity_measurable (θ := 0) (h := 1) (zero_lt_one.trans_le hp) zero_lt_one .a
  have hS := (hasSum_signedTail (t := 0) hM hB le_rfl hτ).summable
  apply hS.congr
  intro j
  change lawPeanoKernel p 1 0 1 .a (0 + τ + (j : ℝ) * τ) = _
  rw [zero_add, (lawPeanoKernel_zero hp hp₂ zero_lt_one zero_lt_one (by positivity)).1]

private theorem convex_limit {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ N, ConvexOn ℝ (Icc 1 (9 / 5)) (f N))
    (hLim : ∀ p ∈ Icc (1 : ℝ) (9 / 5), Tendsto (fun N => f N p) atTop (𝓝 (g p))) :
    ConvexOn ℝ (Icc 1 (9 / 5)) g := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro p hp q hq a b ha hb hab
  exact le_of_tendsto_of_tendsto (hLim _ (convex_Icc _ _ hp hq ha hb hab))
    (((hLim p hp).const_mul a).add ((hLim q hq).const_mul b))
    (Eventually.of_forall (fun N => (hf N).2 hp hq ha hb hab))

theorem pureAStack_exponent_semiconvex {τ : ℝ} (hτ : 0 < τ) (hτ₁ : τ ≤ 1) :
    ConvexOn ℝ (Icc 1 (9 / 5)) (fun p => pureAStack p τ + (17 / 100) * p ^ 2) := by
  let f (N : ℕ) (p : ℝ) := weightedFinitePeano τ (fun t => t) N p + (17 / 100) * p ^ 2
  apply convex_limit (f := f)
  · intro N
    have hArea : (∫ t in (0 : ℝ)..1, t) = 1 / 2 := by rw [integral_id]; norm_num
    have h := weightedFinitePeano_convex (M := 17 / 25) hτ continuousOn_id
      (fun _ ht => ht.1) hArea N (fun t ht p hp => peanoBad_small_mesh hp.1 hp.2 hτ hτ₁ ht.1 N)
    simpa only [f, show (17 / 25 : ℝ) / 4 = 17 / 100 by norm_num] using h
  · intro p hp
    have hSum := pureA_samples_summable hp.1 (hp.2.trans (by norm_num)) hτ
    have h := (hSum.hasSum.tendsto_sum_nat.const_mul τ).add_const ((17 / 100) * p ^ 2)
    simp only [pureAStack, samplingHead] 
    apply h.congr'
    filter_upwards [] with N
    simp only [f, weightedFinitePeano_A hτ (zero_lt_one.trans_le hp.1)]

private theorem weightedFinitePeano_B_limit {p u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hu : 0 < u) :
    Tendsto (fun N => weightedFinitePeano (1 / u) (fun t => 1 - t) N p) atTop (𝓝 (pureBStack p u)) := by
  have ha : 0 < 1 / u := one_div_pos.mpr hu
  have hS := pureBStack_samples_summable hp hp₂ hu
  have h := hS.hasSum.tendsto_sum_nat.const_mul (u ^ (p - 1))
  have hEq (N : ℕ) : weightedFinitePeano (1 / u) (fun t => 1 - t) N p =
      u ^ (p - 1) * ∑ j ∈ Finset.range N, purePeanoB p u ((j : ℝ) + 1) := by
    rw [weightedFinitePeano_B ha (zero_lt_one.trans_le hp), Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    let r := (j : ℝ) + 1
    have hr : 0 < r := by dsimp only [r]; positivity
    have hX : 1 / u + (j : ℝ) * (1 / u) = r / u := by dsimp only [r]; ring
    have hY : r = u * (r / u) := by field_simp [hu.ne']
    have hP : u ^ (p - 1) * u ^ (-p) = 1 / u := by
      rw [← Real.rpow_add hu, show p - 1 + -p = -1 by ring, Real.rpow_neg_one, one_div]
    change 1 / u * purePeanoB p 1 (1 / u + j * (1 / u)) = u ^ (p - 1) * purePeanoB p u r
    have hK := purePeanoB_scale (p := p) hu (div_pos hr hu)
    rw [← hY] at hK
    rw [hX, hK]
    linear_combination -(purePeanoB p 1 (r / u)) * hP
  have hL : pureBStack p u = u ^ (p - 1) * ∑' j : ℕ, purePeanoB p u ((j : ℝ) + 1) := by
    simp only [pureBStack, samplingTail, Nat.cast_add, Nat.cast_one, mul_one, zero_add, one_mul]
  rw [hL]
  exact h.congr' (Eventually.of_forall fun N => (hEq N).symm)

theorem pureBStack_exponent_semiconvex {u : ℝ} (hu : 0 < u) :
    ConvexOn ℝ (Icc 1 (9 / 5)) (fun p => pureBStack p u + (47 / 200) * p ^ 2) := by
  let f (N : ℕ) (p : ℝ) := weightedFinitePeano (1 / u) (fun t => 1 - t) N p + (47 / 200) * p ^ 2
  have ha : 0 < 1 / u := one_div_pos.mpr hu
  apply convex_limit (f := f)
  · intro N
    have hArea : (∫ t in (0 : ℝ)..1, 1 - t) = 1 / 2 := by
      change (∫ t in (0 : ℝ)..1, (fun _ : ℝ => (1 : ℝ)) t - id t) = 1 / 2
      rw [intervalIntegral.integral_sub intervalIntegrable_const (continuous_id.intervalIntegrable (μ := volume) 0 1),
        intervalIntegral.integral_const]
      change (1 - 0) • (1 : ℝ) - (∫ t in (0 : ℝ)..1, t) = 1 / 2
      rw [integral_id]
      norm_num
    have h := weightedFinitePeano_convex (M := 47 / 50) ha
      (continuousOn_const.sub continuousOn_id) (fun _ ht => sub_nonneg.mpr ht.2) hArea N
      (fun t ht p hp => peanoBad_large_mesh hp.1 hp.2 ha ht.1 N)
    simpa only [f, show (47 / 50 : ℝ) / 4 = 47 / 200 by norm_num] using h
  · intro p hp
    exact (weightedFinitePeano_B_limit hp.1 (hp.2.trans (by norm_num)) hu).add_const _

end ACS12.GammaMeasure
