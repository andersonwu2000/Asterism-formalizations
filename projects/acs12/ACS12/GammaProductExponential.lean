import ACS12.GammaMixture
import ACS12.GammaDistributionCore

/-! The actual independent Gamma sum has exponential moments below its first rate. -/
namespace ACS12.GammaMixture
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology

theorem gammaRate_zero_le (j : ℕ) : gammaRate 0 ≤ gammaRate j := by
  unfold gammaRate
  simp only [Nat.cast_zero,zero_add,one_pow,mul_one]
  exact le_mul_of_one_le_right (sq_nonneg _)
    (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) j] : (1:ℝ)≤(j:ℝ)+1))

noncomputable def gammaPartialTotal (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range n, ω j

theorem gammaPartial_exponential {a c : ℝ} (ha : 0 < a) (hc : c < gammaRate 0) (n : ℕ) :
    Integrable (fun ω => Real.exp (c*gammaPartialTotal n ω)) (gammaProduct a) ∧
      (∫ ω, Real.exp (c*gammaPartialTotal n ω) ∂gammaProduct a) =
        ∏ j ∈ range n, (gammaRate j/(gammaRate j-c))^a := by
  letI := gammaProduct_probability ha
  letI : ∀ j : ℕ, IsProbabilityMeasure (gammaMeasure a (gammaRate j)) :=
    fun j => isProbabilityMeasure_gammaMeasure ha (gammaRate_pos j)
  have hcj (j : ℕ) : c < gammaRate j := hc.trans_le (gammaRate_zero_le j)
  have hInd : iIndepFun (fun j (ω : ℕ → ℝ) => Real.exp (c*ω j)) (gammaProduct a) :=
    iIndepFun_infinitePi (P := fun j : ℕ => gammaMeasure a (gammaRate j))
      (X := fun (_ : ℕ) (x : ℝ) => Real.exp (c*x)) (fun _ => by fun_prop)
  have hfin := (hInd.restrict (range n)).integral_fun_prod_eq_prod_integral
    (fun j => by
      change AEStronglyMeasurable (fun ω : ℕ → ℝ => Real.exp (c*ω j)) (gammaProduct a)
      exact (by fun_prop : Measurable (fun ω : ℕ → ℝ => Real.exp (c*ω j))).aestronglyMeasurable)
  have hFactor (j : ℕ) :
      (∫ ω : ℕ → ℝ, Real.exp (c*ω j) ∂gammaProduct a) =
        (gammaRate j/(gammaRate j-c))^a := by
    have h := gammaProduct_coordinate ha j
    have he := integral_map (μ := gammaProduct a) h.measurable.aemeasurable
      (f := fun x : ℝ => Real.exp (c*x)) (by fun_prop)
    rw [h.map_eq] at he
    exact he.symm.trans (GammaDistribution.gammaMeasure_exponential ha (gammaRate_pos j) (hcj j)).2
  have hE : (∫ ω, Real.exp (c*gammaPartialTotal n ω) ∂gammaProduct a) =
      ∏ j ∈ range n, (gammaRate j/(gammaRate j-c))^a := by
    unfold gammaPartialTotal
    simp_rw [mul_sum,Real.exp_sum]
    have hl (ω : ℕ → ℝ) : (∏ j : range n, Real.exp (c*ω j)) = ∏ j ∈ range n, Real.exp (c*ω j) :=
      prod_coe_sort (range n) (fun j : ℕ => Real.exp (c*ω j))
    have hr : (∏ j : range n, ∫ ω : ℕ → ℝ, Real.exp (c*ω j) ∂gammaProduct a) =
        ∏ j ∈ range n, ∫ ω : ℕ → ℝ, Real.exp (c*ω j) ∂gammaProduct a :=
      prod_coe_sort (range n) (fun j : ℕ => ∫ ω : ℕ → ℝ, Real.exp (c*ω j) ∂gammaProduct a)
    simp only [Finset.restrict] at hfin
    simp_rw [hl,hr,hFactor] at hfin
    exact hfin
  have hPos : 0 < ∏ j ∈ range n, (gammaRate j/(gammaRate j-c))^a :=
    prod_pos fun j _ => Real.rpow_pos_of_pos (div_pos (gammaRate_pos j) (sub_pos.mpr (hcj j))) a
  exact ⟨Integrable.of_integral_ne_zero (hE ▸ hPos.ne'),hE⟩

end ACS12.GammaMixture
