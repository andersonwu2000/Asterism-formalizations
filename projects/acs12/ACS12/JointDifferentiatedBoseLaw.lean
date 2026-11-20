import ACS12.JointDifferentiatedMoment
import ACS12.NativeJointBoseEntrance
import ACS12.ComplexBoseHolomorphy
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected

/-! The ordinary beta entrance identifies each differentiated strip with the original Bose row. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter Metric
open scoped Topology
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def jointDifferentiatedScale (α : ℂ) : ℂ :=
  (4:ℂ)^(jointDifferentiatedExponent α)/(3*Complex.Gamma (α/2))

theorem jointDifferentiatedScale_differentiableAt {α : ℂ} (hα : 0 < α.re) :
    DifferentiableAt ℂ jointDifferentiatedScale α := by
  have hPos : 0 < (α/2).re := by simp; linarith only [hα]
  have hAvoid (n : ℕ) : α/2 ≠ -(n:ℂ) := by
    intro he
    have h := congrArg Complex.re he
    rw [Complex.neg_re,Complex.natCast_re] at h
    linarith only [h,hPos,Nat.cast_nonneg (α := ℝ) n]
  have hGamma := (Complex.differentiableAt_Gamma _ hAvoid).comp α
    (by fun_prop : DifferentiableAt ℂ (fun a : ℂ => a/2) α)
  have hNum : DifferentiableAt ℂ (fun a : ℂ => (4:ℂ)^(jointDifferentiatedExponent a)) α := by
    have hEq : (fun a : ℂ => (4:ℂ)^(jointDifferentiatedExponent a)) =
        (fun a => Complex.exp (Complex.log 4*jointDifferentiatedExponent a)) := by
      funext a
      rw [Complex.cpow_def_of_ne_zero (by norm_num : (4:ℂ)≠0)]
    rw [hEq]
    unfold jointDifferentiatedExponent
    fun_prop
  exact hNum.div (hGamma.const_mul 3) (mul_ne_zero (by norm_num) (Complex.Gamma_ne_zero_of_re_pos hPos))

theorem jointDifferentiatedScale_analytic {α : ℂ} (hα : 0 < α.re) : AnalyticAt ℂ jointDifferentiatedScale α := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hα] with a ha
  exact jointDifferentiatedScale_differentiableAt ha


theorem jointDifferentiatedScale_real {p : ℝ} (hp : 0 < p) :
    jointDifferentiatedScale (p:ℂ) = (nativeJointScale p:ℂ) := by
  have hExp : jointDifferentiatedExponent (p:ℂ) = (((p-2)/2:ℝ):ℂ) := by
    unfold jointDifferentiatedExponent
    push_cast
    rfl
  unfold jointDifferentiatedScale nativeJointScale
  rw [hExp,show (4:ℂ) = ((4:ℝ):ℂ) by norm_num,
    ← Complex.ofReal_cpow (by norm_num : (0:ℝ)≤4)]
  have hArg : (p:ℂ)/2 = ((p/2:ℝ):ℂ) := by push_cast; rfl
  rw [hArg,Complex.Gamma_ofReal]
  push_cast
  rfl

noncomputable def jointDifferentiatedBoseModel (k : ℕ) (N : ℝ) (α : ℂ) : ℂ :=
  (N:ℂ)^2*jointDifferentiatedScale α*jointDifferentiatedMoment (N^2) k α

theorem jointDifferentiatedBoseModel_analytic {α : ℂ} (hα : 0 < α.re) (k : ℕ)
    (hStrip : (jointDifferentiatedExponent α).re < (k:ℝ)) (N : ℝ) :
    AnalyticAt ℂ (jointDifferentiatedBoseModel k N) α := by
  have hConst : AnalyticAt ℂ (fun _ : ℂ => (N:ℂ)^2) α := by fun_prop
  exact (hConst.mul (jointDifferentiatedScale_analytic hα)).mul
    (jointDifferentiatedMoment_analytic (sq_nonneg N) hα k hStrip)

theorem jointDifferentiatedBoseModel_entrance {p N : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (hN : 0 < N) (k : ℕ) : jointDifferentiatedBoseModel k N (p:ℂ) = (boseRow p N:ℂ) := by
  have hβ : (p-2)/2 < (k:ℝ) := by
    have hk := Nat.cast_nonneg (α:=ℝ) k
    linarith only [hp₁,hk]
  unfold jointDifferentiatedBoseModel
  rw [jointDifferentiatedScale_real hp,jointDifferentiatedMoment_real hp (sq_nonneg N) k hβ]
  have h := congrArg (fun x : ℝ => (x:ℂ)) (boseRow_joint_ordinary_entrance hp hp₁ hN)
  push_cast at h
  exact h.symm

private theorem analytic_differentiated_strip_identity (k : ℕ) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {a : ℂ | 0 < a.re ∧ (jointDifferentiatedExponent a).re < (k:ℝ)})
    (hg : AnalyticOnNhd ℂ g {a : ℂ | 0 < a.re ∧ (jointDifferentiatedExponent a).re < (k:ℝ)})
    (hEntrance : ∀ p : ℝ, 0 < p → p < 1 → f (p:ℂ)=g (p:ℂ)) :
    EqOn f g {a : ℂ | 0 < a.re ∧ (jointDifferentiatedExponent a).re < (k:ℝ)} := by
  have hAccum : (1/2:ℂ) ∈ closure ({a : ℂ | f a = g a}\{(1/2:ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ := min (ε/2) (1/4)
    have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
    have hδε : δ ≤ ε/2 := min_le_left _ _
    have hδ₁ : δ ≤ 1/4 := min_le_right _ _
    let p := (1/2:ℝ)+δ
    have hp : 0 < p := by dsimp only [p]; linarith only [hδ]
    have hp₁ : p < 1 := by dsimp only [p]; linarith only [hδ₁]
    refine ⟨(p:ℂ),⟨hEntrance p hp hp₁,?_⟩,?_⟩
    · intro he
      have he' : (p:ℂ) = (1/2:ℂ) := Set.mem_singleton_iff.mp he
      have hh := congrArg Complex.re he'
      simp only [Complex.ofReal_re,Complex.div_ofNat_re,Complex.one_re] at hh
      dsimp only [p] at hh
      linarith only [hh,hδ]
    · have he : (1/2:ℂ) = ((1/2:ℝ):ℂ) := by norm_num
      rw [he,dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      have hpδ : p-(1/2:ℝ) = δ := by dsimp only [p]; ring
      rw [abs_sub_comm,hpδ,abs_of_pos hδ]
      linarith only [hδε,hε]
  have hSet : {a : ℂ | 0 < a.re ∧ (jointDifferentiatedExponent a).re < (k:ℝ)} =
      {a : ℂ | 0 < a.re} ∩ {a : ℂ | a.re < 2*((k:ℝ)+1)} := by
    ext a
    simp only [mem_setOf_eq,mem_inter_iff,jointDifferentiatedExponent_re]
    constructor <;> intro h <;> constructor <;> linarith only [h.1,h.2]
  have hConv : Convex ℝ {a : ℂ | 0 < a.re ∧ (jointDifferentiatedExponent a).re < (k:ℝ)} := by
    rw [hSet]
    exact (convex_halfSpace_re_gt (r:=0)).inter (convex_halfSpace_re_lt (r:=2*((k:ℝ)+1)))
  have hHalf : (1/2:ℂ) ∈ {a : ℂ | 0 < a.re ∧ (jointDifferentiatedExponent a).re < (k:ℝ)} := by
    simp only [mem_setOf_eq,jointDifferentiatedExponent_re]
    norm_num
    have hk := Nat.cast_nonneg (α:=ℝ) k
    linarith only [hk]
  exact hf.eqOn_of_preconnected_of_mem_closure hg hConv.isPreconnected hHalf hAccum

theorem complexBoseRow_eq_differentiatedModel {α : ℂ} {N : ℝ} (hα : 0 < α.re) (hN : 0 < N)
    (k : ℕ) (hStrip : (jointDifferentiatedExponent α).re < (k:ℝ)) :
    complexBoseRow N α = jointDifferentiatedBoseModel k N α := by
  apply analytic_differentiated_strip_identity k
    (fun a ha => complexBoseRow_analytic ha.1 hN)
    (fun a ha => jointDifferentiatedBoseModel_analytic ha.1 k ha.2 N)
    (fun p hp hp₁ => by rw [complexBoseRow_real,jointDifferentiatedBoseModel_entrance hp hp₁ hN])
    ⟨hα,hStrip⟩

theorem boseRow_joint_differentiated {p N : ℝ} (hp : 0 < p) (hN : 0 < N) :
    boseRow p N = N^2*nativeJointScale p*
      ∫ ω, nativeJointEnergy (N^2) ω^((p-2)/2) ∂nativeJointMeasure p := by
  let k := Nat.ceil ((p-2)/2)+1
  have hβ : (p-2)/2 < (k:ℝ) := by
    have hCeil := Nat.le_ceil ((p-2)/2)
    dsimp [k]
    push_cast
    linarith only [hCeil]
  have hStrip : (jointDifferentiatedExponent (p:ℂ)).re < (k:ℝ) := by
    simpa only [jointDifferentiatedExponent_re,Complex.ofReal_re] using hβ
  have h := complexBoseRow_eq_differentiatedModel hp hN k hStrip
  rw [complexBoseRow_real] at h
  unfold jointDifferentiatedBoseModel at h
  rw [jointDifferentiatedScale_real hp,jointDifferentiatedMoment_real hp (sq_nonneg N) k hβ] at h
  apply Complex.ofReal_injective
  convert h using 1 <;> push_cast <;> rfl

theorem jointDifferentiatedMoment_three_real {p z : ℝ} (hp : 2 ≤ p) (hp₆ : p ≤ 6) (hz : 0 ≤ z) :
    jointDifferentiatedMoment z 3 (p:ℂ) =
      ((∫ ω, nativeJointEnergy z ω^((p-2)/2) ∂nativeJointMeasure p:ℝ):ℂ) :=
  jointDifferentiatedMoment_real (by linarith only [hp]) hz 3 (by norm_num; linarith only [hp₆])

end ACS12.NativeCells
