import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! Parameter analyticity of ordinary derivatives follows from the same joint analytic function. -/
namespace ACS12
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

private noncomputable def verticalCLM : ℂ →L[ℂ] ℂ × ℂ :=
  (0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)

noncomputable def verticalDerivative (F : ℂ × ℂ → ℂ) (k : ℕ) (a : ℂ × ℂ) : ℂ :=
  iteratedFDeriv ℂ k F a (fun _ => (0,1))

theorem verticalDerivative_eq {F : ℂ × ℂ → ℂ} {a t : ℂ}
    (hF : AnalyticAt ℂ F (a,t)) (k : ℕ) :
    verticalDerivative F k (a,t) = iteratedDeriv k (fun u => F (a,u)) t := by
  obtain ⟨q,r,hq⟩ := hF
  have hShift : HasFPowerSeriesAt (fun v : ℂ × ℂ => F (v - -(a,t))) q (verticalCLM 0) := by
    simpa only [verticalCLM,ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.id_apply,add_neg_cancel] using hq.hasFPowerSeriesAt.comp_sub (-(a,t))
  have hTrace : HasFPowerSeriesAt (fun u : ℂ => F (a,u+t))
      (q.compContinuousLinearMap verticalCLM) 0 := by
    convert hShift.compContinuousLinearMap (u:=verticalCLM) using 1
    ext u
    simp [Function.comp_apply,verticalCLM]
  have hJoint := hq.factorial_smul ((0:ℂ),(1:ℂ)) k
  obtain ⟨rT,hTraceOn⟩ := hTrace
  have hOne := hTraceOn.factorial_smul (1:ℂ) k
  simp only [FormalMultilinearSeries.compContinuousLinearMap_apply,Function.comp_def,verticalCLM,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply,
    ContinuousMultilinearMap.smul_apply,nsmul_eq_mul] at hOne hJoint
  have hTraceD : iteratedFDeriv ℂ k (fun u : ℂ => F (a,u+t)) 0 (fun _=>1) =
      iteratedDeriv k (fun u=>F (a,u)) t := by
    change iteratedDeriv k (fun u=>F (a,u+t)) 0 = _
    have hEq := congrFun (iteratedDeriv_comp_add_const (n:=k) (f:=fun u => F (a,u)) (s:=t)) 0
    simpa only [zero_add] using hEq
  dsimp only [verticalDerivative]
  rw [←hJoint,←hTraceD,←hOne]

private noncomputable def verticalEvaluation (k : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => ℂ × ℂ) ℂ →L[ℂ] ℂ :=
  ({toFun:=fun f=>f (fun _=>(0,1)),map_add':=by intro f g; simp,
    map_smul':=by intro c f; simp} :
      ContinuousMultilinearMap ℂ (fun _ : Fin k => ℂ × ℂ) ℂ →ₗ[ℂ] ℂ).mkContinuous
    (∏ _ : Fin k, ‖((0:ℂ),(1:ℂ))‖) (fun f => by simpa only [mul_comm] using f.le_opNorm (fun _=>(0,1)))

theorem verticalDerivative_analytic {F : ℂ × ℂ → ℂ} {a : ℂ × ℂ}
    (hF : AnalyticAt ℂ F a) (k : ℕ) : AnalyticAt ℂ (verticalDerivative F k) a := by
  have hOn : AnalyticOnNhd ℂ F {a} := fun x hx => by have h : x=a := hx; subst x; exact hF
  have hD := hOn.iteratedFDeriv k a (by simp)
  exact (verticalEvaluation k).analyticAt _ |>.comp hD

theorem section_iteratedDeriv_analytic {F : ℂ × ℂ → ℂ} {a t : ℂ}
    (hF : AnalyticAt ℂ F (a,t)) (k : ℕ) :
    AnalyticAt ℂ (fun b => iteratedDeriv k (fun u => F (b,u)) t) a := by
  have hArg : AnalyticAt ℂ (fun b : ℂ => (b,t)) a := by fun_prop
  have h := (verticalDerivative_analytic hF k).comp_of_eq' hArg rfl
  apply h.congr
  have hE := hF.eventually_analyticAt
  have hT : Tendsto (fun b : ℂ => (b,t)) (𝓝 a) (𝓝 (a,t)) :=
    (continuous_id.prodMk continuous_const).tendsto a
  filter_upwards [hT.eventually hE] with b hb
  exact verticalDerivative_eq hb k

end ACS12
