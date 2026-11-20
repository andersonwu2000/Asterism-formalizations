import ACS12.GammaTotalExponential
import ACS12.ExponentialPowerMoments

/-! Exact second moment of the same independent Gamma sum, by finite variance addition. -/
namespace ACS12.GammaMixture
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem gammaMeasure_natMoment {a r : ℝ} (ha : 0<a) (hr : 0<r) (k : ℕ) :
    Integrable (fun x : ℝ=>x^k) (gammaMeasure a r) ∧
      (∫ x : ℝ,x^k ∂gammaMeasure a r)=Real.Gamma (a+k)/Real.Gamma a/r^k := by
  have hak : 0<a+(k:ℝ):=add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg k)
  have hE : (∫ x : ℝ,x^k ∂gammaMeasure a r)=Real.Gamma (a+k)/Real.Gamma a/r^k := by
    rw [GammaDistribution.integral_gammaMeasure_eq ha hr]
    have hPoint (x : ℝ) (hx : 0<x) :
        (r^a/Real.Gamma a*x^(a-1)*Real.exp (-(r*x)))*x^k=
          (r^a/Real.Gamma a)*(x^(a+(k:ℝ)-1)*Real.exp (-r*x)) := by
      rw [show a+(k:ℝ)-1=(a-1)+(k:ℝ) by ring,Real.rpow_add hx,Real.rpow_natCast]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx=>hPoint x hx),integral_const_mul,
      GammaDeficit.gamma_exp_integral hak hr,Real.rpow_neg hr.le,
      Real.rpow_add hr,Real.rpow_natCast]
    field_simp [(Real.rpow_pos_of_pos hr a).ne',(Real.Gamma_pos_of_pos ha).ne']
    <;> ring
  refine ⟨Integrable.of_integral_ne_zero (hE ▸ ?_),hE⟩
  exact (div_pos (div_pos (Real.Gamma_pos_of_pos hak) (Real.Gamma_pos_of_pos ha)) (pow_pos hr k)).ne'

private theorem gammaCoordinate_moments {a : ℝ} (ha : 0<a) (j : ℕ) :
    Integrable (fun ω : ℕ→ℝ=>ω j) (gammaProduct a) ∧
      Integrable (fun ω : ℕ→ℝ=>(ω j)^2) (gammaProduct a) ∧
      (∫ ω : ℕ→ℝ,ω j ∂gammaProduct a)=a/gammaRate j ∧
      (∫ ω : ℕ→ℝ,(ω j)^2 ∂gammaProduct a)=a*(a+1)/(gammaRate j)^2 := by
  have hMap:=gammaProduct_coordinate ha j
  have hIntegral (k : ℕ) : (∫ ω : ℕ→ℝ,(ω j)^k ∂gammaProduct a)=
      (∫ x : ℝ,x^k ∂gammaMeasure a (gammaRate j)) := by
    have h:=integral_map (μ:=gammaProduct a) hMap.measurable.aemeasurable
      (f:=fun x : ℝ=>x^k) (by fun_prop)
    rw [hMap.map_eq] at h
    exact h.symm
  have h₁:=gammaMeasure_natMoment ha (gammaRate_pos j) 1
  have h₂:=gammaMeasure_natMoment ha (gammaRate_pos j) 2
  have hI₁ : Integrable (fun ω : ℕ→ℝ=>ω j) (gammaProduct a):=by
    simpa only [pow_one] using hMap.integrable_comp_of_integrable h₁.1
  have hI₂:=hMap.integrable_comp_of_integrable h₂.1
  refine ⟨hI₁,hI₂,?_,?_⟩
  · have h:=hIntegral 1
    simp only [pow_one] at h
    rw [show (∫ x : ℝ,x ∂gammaMeasure a (gammaRate j))=a/gammaRate j by
      simpa only [Nat.cast_one,pow_one,Real.Gamma_add_one ha.ne',mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos ha).ne'] using h₁.2] at h
    exact h
  · have h:=hIntegral 2
    rw [h₂.2] at h
    convert h using 1
    rw [show a+(2:ℕ)=a+1+1 by push_cast;ring,Real.Gamma_add_one (by positivity : a+1≠0),Real.Gamma_add_one ha.ne']
    field_simp [(Real.Gamma_pos_of_pos ha).ne']
    <;> ring

private theorem gammaCoordinate_product {a : ℝ} (ha : 0<a) (i j : ℕ) :
    Integrable (fun ω : ℕ→ℝ=>ω i*ω j) (gammaProduct a) ∧
      (∫ ω : ℕ→ℝ,ω i*ω j ∂gammaProduct a)=
        (a/gammaRate i)*(a/gammaRate j)+(if i=j then a/(gammaRate i)^2 else 0) := by
  letI:=gammaProduct_probability ha
  letI : ∀ j : ℕ, IsProbabilityMeasure (gammaMeasure a (gammaRate j)):=
    fun j=>isProbabilityMeasure_gammaMeasure ha (gammaRate_pos j)
  by_cases hij : i=j
  · subst j
    have h:=gammaCoordinate_moments ha i
    refine ⟨by simpa only [←pow_two] using h.2.1,?_⟩
    rw [show (fun ω : ℕ→ℝ=>ω i*ω i)=(fun ω : ℕ→ℝ=>(ω i)^2) by funext ω;ring,h.2.2.2,if_pos rfl]
    field_simp [(gammaRate_pos i).ne']
    <;> ring
  · have hInd : iIndepFun (fun j (ω : ℕ→ℝ)=>ω j) (gammaProduct a):=
      iIndepFun_infinitePi (P:=fun j : ℕ=>gammaMeasure a (gammaRate j))
        (X:=fun (_ : ℕ) (x : ℝ)=>x) (fun _=>measurable_id)
    have hPair:=hInd.indepFun hij
    refine ⟨hPair.integrable_mul (gammaCoordinate_moments ha i).1 (gammaCoordinate_moments ha j).1,?_⟩
    rw [hPair.integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable,(gammaCoordinate_moments ha i).2.2.1,
      (gammaCoordinate_moments ha j).2.2.1,if_neg hij,add_zero]

theorem gammaFinite_second {a : ℝ} (ha : 0<a) (s : Finset ℕ) :
    Integrable (fun ω : ℕ→ℝ=>(∑ j∈s,ω j)^2) (gammaProduct a) ∧
      (∫ ω : ℕ→ℝ,(∑ j∈s,ω j)^2 ∂gammaProduct a)=
        (∑ j∈s,a/gammaRate j)^2+∑ j∈s,a/(gammaRate j)^2 := by
  have hF : (fun ω : ℕ→ℝ=>(∑ j∈s,ω j)^2)=
      (fun ω=>∑ i∈s,∑ j∈s,ω i*ω j) := by
    funext ω
    rw [pow_two,Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hI:=integrable_finsetSum s (fun i _=>integrable_finsetSum s
    (fun j _=>(gammaCoordinate_product ha i j).1))
  refine ⟨hF.symm ▸ hI,?_⟩
  rw [hF,integral_finsetSum s (fun i _=>integrable_finsetSum s
    (fun j _=>(gammaCoordinate_product ha i j).1))]
  simp_rw [integral_finsetSum s (fun j _=>(gammaCoordinate_product ha _ j).1)]
  simp_rw [(gammaCoordinate_product ha _ _).2,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ]
  rw [pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum,Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos hi]

 theorem gammaRate_inverse_square_hasSum :
    HasSum (fun j : ℕ=>1/(gammaRate j)^2) (1/1440) := by
  have hs:=hasSum_zeta_four.summable
  have hShift: Summable (fun j : ℕ=>1/((j:ℝ)+1)^4):=by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have hZ:=hasSum_zeta_four.summable.tsum_eq_zero_add
  norm_num only [Nat.cast_zero,Nat.cast_add,Nat.cast_one,zero_pow (by decide : (4:ℕ)≠0),div_zero,zero_add] at hZ
  have hTerm (j : ℕ) : 1/(gammaRate j)^2=(1/(2*Real.pi)^4)*(1/((j:ℝ)+1)^4) := by
    unfold gammaRate
    field_simp [Real.pi_ne_zero,(show (j:ℝ)+1≠0 by positivity)]
    <;> ring
  have hS:Summable (fun j : ℕ=>1/(gammaRate j)^2):=
    (hShift.mul_left (1/(2*Real.pi)^4)).congr (fun j=>(hTerm j).symm)
  have hT : (∑' j : ℕ,1/(gammaRate j)^2)=1/1440 := by
    simp_rw [hTerm]
    rw [tsum_mul_left,←hZ,hasSum_zeta_four.tsum_eq]
    field_simp [Real.pi_ne_zero]
    <;> ring
  exact hT ▸ hS.hasSum


private theorem gammaCoordinate_ae_nonneg {a : ℝ} (ha : 0<a) (j : ℕ) :
    ∀ᵐ ω ∂gammaProduct a,0≤ω j := by
  have hMap:=gammaProduct_coordinate ha j
  have hDist : ∀ᵐ x : ℝ ∂gammaMeasure a (gammaRate j),0≤x := by
    unfold gammaMeasure
    apply (ae_withDensity_iff (measurable_gammaPDFReal a (gammaRate j)).ennreal_ofReal).mpr
    exact Eventually.of_forall fun x hpdf=>by
      by_contra! hx
      exact hpdf (gammaPDF_of_neg hx)
  have h : ∀ᵐ x : ℝ ∂(gammaProduct a).map (fun ω : ℕ→ℝ=>ω j),0≤x := by
    rw [hMap.map_eq]
    exact hDist
  exact (ae_map_iff hMap.measurable.aemeasurable measurableSet_Ici).mp h

 theorem gammaTotal_square_integrable {a : ℝ} (ha : 0<a) :
    Integrable (fun ω=>gammaTotal ω^2) (gammaProduct a) := by
  letI:=gammaProduct_probability ha
  let c:=gammaRate 0/2
  have hc : 0<c := div_pos (gammaRate_pos 0) zero_lt_two
  have hExp:=gammaTotal_exponential_integrable ha hc.le
    (by unfold c;linarith only [gammaRate_pos 0] : c<gammaRate 0)
  have h:=ACS12.integrable_rpow_of_exponential measurable_gammaTotal
    (Eventually.of_forall fun _=>ENNReal.toReal_nonneg) hc hExp (by norm_num : (0:ℝ)≤2)
  simpa only [Real.rpow_two] using h

 theorem gammaTotal_second_integral {a : ℝ} (ha : 0<a) :
    (∫ ω,gammaTotal ω^2 ∂gammaProduct a)=(a/24)^2+a/1440 := by
  letI:=gammaProduct_probability ha
  have hLimit : Tendsto (fun n : ℕ=>∫ ω,gammaPartialTotal n ω^2 ∂gammaProduct a)
      atTop (𝓝 (∫ ω,gammaTotal ω^2 ∂gammaProduct a)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω=>gammaTotal ω^2)
    · intro n
      exact (by unfold gammaPartialTotal;fun_prop : Measurable (fun ω=>gammaPartialTotal n ω^2)).aestronglyMeasurable
    · exact gammaTotal_square_integrable ha
    · intro n
      filter_upwards [gammaProduct_ae_hasSum ha,
        eventually_countable_forall.mpr (gammaCoordinate_ae_nonneg ha)] with ω hω hPos
      have hP : 0≤gammaPartialTotal n ω := Finset.sum_nonneg fun j _=>hPos j
      have hLe : gammaPartialTotal n ω≤gammaTotal ω := by
        rw [←hω.tsum_eq]
        exact hω.summable.sum_le_tsum (range n) (fun j _=>hPos j)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ hP hLe 2
    · filter_upwards [gammaProduct_ae_hasSum ha] with ω hω
      exact hω.tendsto_sum_nat.pow 2
  have hMean : Tendsto (fun n : ℕ=>∑ j∈range n,a/gammaRate j) atTop (𝓝 (a/24)) := by
    have h:=gammaRate_inverse_hasSum.mul_left a
    simp only [mul_one_div] at h
    convert h.tendsto_sum_nat using 1 <;> ring
  have hVar : Tendsto (fun n : ℕ=>∑ j∈range n,a/(gammaRate j)^2) atTop (𝓝 (a/1440)) := by
    have h:=gammaRate_inverse_square_hasSum.mul_left a
    simp only [mul_one_div] at h
    convert h.tendsto_sum_nat using 1 <;> ring
  have hValue : Tendsto (fun n : ℕ=>(∑ j∈range n,a/gammaRate j)^2+
      ∑ j∈range n,a/(gammaRate j)^2) atTop (𝓝 ((a/24)^2+a/1440)) :=
    (hMean.pow 2).add hVar
  have hEq (n : ℕ) : (∫ ω,gammaPartialTotal n ω^2 ∂gammaProduct a)=
      (∑ j∈range n,a/gammaRate j)^2+∑ j∈range n,a/(gammaRate j)^2 :=
    (gammaFinite_second ha (range n)).2
  exact tendsto_nhds_unique (hLimit.congr hEq) hValue

end ACS12.GammaMixture
