import Verification.ExternalActuatorContract
import Mathlib.Tactic.NormNum
open ExternalActuatorContract
set_option backward.isDefEq.respectTransparency false

private def auth (_ : Nat) : Prop := True
private def conf (_ : Nat) : Prop := True
private def a : State Nat := reserve initial 7
private def sent : State Nat := issue a 7

example : a.journal 7 = some .armed := by simp [a, reserve]
example : a.permit 7 = true := by simp [a, reserve]
example : sent.journal 7 = some .armed := by simp [sent, issue, a, reserve]
example : sent.permit 7 = false := by simp [sent, issue]
example : (recover a).permit 7 = false := rfl
example : (recover sent).permit 7 = false := rfl
example : ¬ Step auth conf (recover a) (.issue 7) sent := no_issue_after_recovery _ _ _ _ _
example (t : State Nat) : ¬ Step auth conf sent (.reserve 7) t := by
  intro h; cases h with | reserve _ hn => simp [sent, a, issue, reserve] at hn
example (t : State Nat) : ¬ Step auth conf initial (.issue 7) t := by
  intro h; cases h with | issue ha _ => simp [initial] at ha
example : ¬ Step (fun _ : Nat => False) conf initial (.reserve 7) a := by
  intro h; cases h with | reserve ha _ => exact ha
example : Run auth conf initial (preCrashEvents 7) (preCrashState 7) :=
  pre_crash_reachable _ _ _ trivial
example : Run auth conf initial (postCrashEvents 7) (postCrashState 7) :=
  post_crash_reachable _ _ _ trivial
example : observe (preCrashState 7) false = observe (postCrashState 7) false := rfl
example : dispatchCount (postCrashEvents 7) 7 = 1 := post_crash_dispatch_count _
example : dispatchCount (preCrashEvents 7) 7 = 0 := pre_crash_dispatch_count _
example : ¬ (∃ s : State Nat, Run auth conf initial
    [.reserve 7, .issue 7, .recover, .issue 7] s) := by
  rintro ⟨s, hs⟩
  have hb := at_most_one_dispatch hs 7
  have hn : ¬ dispatchCount ([.reserve 7, .issue 7, .recover, .issue 7] : List (Event Nat)) 7 ≤ 1 := by decide
  exact hn hb

/-- Other actions cannot make the older action fresh again. -/
private def interleaved : State Nat := issue (reserve sent 9) 9
private theorem interleaved_run : Run auth conf initial
    [.reserve 7, .issue 7, .reserve 9, .issue 9] interleaved := by
  have h1 : Run auth conf initial [.reserve 7] a := .snoc .nil (.reserve trivial rfl)
  have h2 : Run auth conf initial [.reserve 7, .issue 7] sent :=
    .snoc h1 (.issue (by simp [a, reserve]) (by simp [a, reserve]))
  have h3 : Run auth conf initial [.reserve 7, .issue 7, .reserve 9] (reserve sent 9) :=
    .snoc h2 (.reserve trivial (by simp [sent, a, issue, reserve, initial]))
  exact .snoc h3 (.issue (by simp [reserve]) (by simp [reserve]))

example : ¬ Step auth conf interleaved (.reserve 7) (reserve interleaved 7) := by
  intro h; cases h with | reserve _ hn => simp [interleaved, sent, a, reserve, issue] at hn
example : dispatchCount [.reserve 7, .issue 7, .reserve 9, .issue 9] 7 ≤ 1 :=
  at_most_one_dispatch interleaved_run 7

-- Evaluation is only for pure model data; no driver, device or scenario runner.
def main : IO Unit := do
  unless dispatchCount (preCrashEvents (7 : Nat)) 7 == 0 do throw (IO.userError "pre count")
  unless dispatchCount (postCrashEvents (7 : Nat)) 7 == 1 do throw (IO.userError "post count")
  unless (recover a).permit 7 == false do throw (IO.userError "recovery permit")
  unless interleaved.journal 7 == some .armed do throw (IO.userError "old history lost")
  IO.println "EXTERNAL_ACTUATOR_OK 4"
