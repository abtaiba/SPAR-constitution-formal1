/-
  lang1.lean — small1, formalized from the natural-language specification
  (small1_training_manual.txt).

  This file models the *world the manual talks about*: parties, requests,
  attempts, responses, preparation and sessions. Each rule is then a predicate
  on a session. Every definition quotes the manual sentence it formalizes.

  Where the manual is vague ("immediately", "while the request is still
  fresh") the vagueness becomes an explicit parameter (`Standards`) rather
  than being resolved silently.

  Compare formal1.lean, which formalizes the same rules from small1.json as
  propositional formulas.

  Check with:  lean lang1.lean        (Lean 4, no dependencies)
-/

namespace Small1.Lang

/-! ## Decidability helper -/

/-- "for every x in the list" is decidable when the property is. (Lean core does not provide
this instance in the form the rules need, so it is defined here.) -/
def decForallMem {α : Type} (p : α → Prop) [DecidablePred p] :
    (l : List α) → Decidable (∀ x ∈ l, p x)
  | [] => isTrue (fun _ h => nomatch h)
  | a :: l =>
    if ha : p a then
      match decForallMem p l with
      | isTrue hl  => isTrue (fun x hx => by
          cases hx with
          | head => exact ha
          | tail _ h => exact hl x h)
      | isFalse hl => isFalse (fun h => hl (fun x hx => h x (.tail _ hx)))
    else isFalse (fun h => ha (h a (.head _)))

instance {α : Type} (p : α → Prop) [DecidablePred p] (l : List α) : Decidable (∀ x ∈ l, p x) :=
  decForallMem p l

theorem eq_nil_of_isEmpty {α : Type} {l : List α} (h : l.isEmpty = true) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ => cases h

theorem mem_append_cons_cons {α : Type} (pre post : List α) (a b : α) :
    b ∈ pre ++ a :: b :: post := by
  induction pre with
  | nil => exact .tail _ (.head _)
  | cons _ _ ih => exact .tail _ ih

/-! ## §1 Who is involved -/

/-- "This manual describes training between two parties." -/
inductive Party
  | user
  | agent
  deriving Repr, DecidableEq

/-- "The user is the trainer. The agent is the learner." -/
inductive Role
  | trainer
  | learner
  deriving Repr, DecidableEq

def Party.role : Party → Role
  | .user  => .trainer
  | .agent => .learner

/-! ## §2 Key terms -/

/-- "A request is a single instruction the user gives the agent during a session." -/
structure Request where
  id          : Nat
  instruction : String
  deriving Repr

/-- "A success is when the agent carries out a request correctly. A failure is when it does not." -/
inductive Outcome
  | success
  | failure
  deriving Repr, DecidableEq

/-- The agent produces the outcome; the user produces the response. -/
def Outcome.actor (_ : Outcome) : Party := .agent

/-- "A reward is any response that the agent values and that makes a success more likely next
time, such as praise." -/
structure RewardAct where
  description            : String
  valuedByAgent          : Bool
  makesSuccessMoreLikely : Bool
  deriving Repr

/-- Whether an act meets the manual's definition of a reward. -/
def RewardAct.isReward (r : RewardAct) : Bool :=
  r.valuedByAgent && r.makesSuccessMoreLikely

/-- "... such as praise." -/
def praise : RewardAct := ⟨"praise", true, true⟩

theorem praise_isReward : praise.isReward = true := rfl

/-- "A correction is a brief, calm response that shows the agent what it did wrong and guides it
to the right behaviour." -/
structure CorrectionAct where
  description            : String
  brief                  : Bool
  calm                   : Bool
  showsWhatWentWrong     : Bool
  guidesToRightBehaviour : Bool
  deriving Repr

/-- Whether an act meets all four parts of the manual's definition of a correction. -/
def CorrectionAct.isCorrection (c : CorrectionAct) : Bool :=
  c.brief && c.calm && c.showsWhatWentWrong && c.guidesToRightBehaviour

/-- Everything the user might do in reply to an attempt. `punishment` is included so that
"A correction is not a punishment." can be stated and enforced. -/
inductive Response
  | reward     (r : RewardAct)
  | correction (c : CorrectionAct)
  | punishment (description : String)
  | none
  deriving Repr

/-- Responses are the user's acts: "the user must reward it", "the user must give a correction". -/
def Response.actor (_ : Response) : Party := .user

/-- A response that genuinely counts as a reward under §2. -/
def Response.isGenuineReward : Response → Bool
  | .reward r => r.isReward
  | _         => false

/-- A response that genuinely counts as a correction under §2. -/
def Response.isGenuineCorrection : Response → Bool
  | .correction c => c.isCorrection
  | _             => false

def Response.isPunishment : Response → Bool
  | .punishment _ => true
  | _             => false

/-- "A correction is not a punishment." -/
theorem correction_not_punishment (r : Response) :
    r.isGenuineCorrection = true → r.isPunishment = false := by
  cases r <;> simp [Response.isGenuineCorrection, Response.isPunishment]

/-- A reward is not a punishment either. -/
theorem reward_not_punishment (r : Response) :
    r.isGenuineReward = true → r.isPunishment = false := by
  cases r <;> simp [Response.isGenuineReward, Response.isPunishment]

/-- One response cannot be both a reward and a correction. -/
theorem reward_correction_exclusive (r : Response) :
    ¬ (r.isGenuineReward = true ∧ r.isGenuineCorrection = true) := by
  cases r <;> simp [Response.isGenuineReward, Response.isGenuineCorrection]

/-! ### Timing -/

/-- The manual's timing words are vague. These thresholds (in abstract time steps) make them
explicit, so the rules can be checked against different readings of "immediately" and
"still fresh". -/
structure Standards where
  /-- largest delay that still counts as "immediately" (Rule 1) -/
  immediately : Nat
  /-- how long a request stays "still fresh" (Rule 2) -/
  freshFor    : Nat
  deriving Repr

/-! ### Attempts and exchanges -/

/-- One try by the agent at a request, and the user's reply to it. -/
structure Attempt where
  outcome  : Outcome
  response : Response
  /-- time between the outcome and the user's response -/
  delay    : Nat
  deriving Repr

/-- "the user must reward it" + "Give the reward immediately after the success." -/
def Attempt.RewardedImmediately (std : Standards) (a : Attempt) : Prop :=
  a.response.isGenuineReward = true ∧ a.delay ≤ std.immediately

/-- "the user must give a correction" + "Correct the agent right away, while the request is
still fresh." -/
def Attempt.CorrectedWhileFresh (std : Standards) (a : Attempt) : Prop :=
  a.response.isGenuineCorrection = true ∧ a.delay ≤ std.freshFor

instance (std : Standards) (a : Attempt) : Decidable (a.RewardedImmediately std) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (std : Standards) (a : Attempt) : Decidable (a.CorrectedWhileFresh std) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A request together with the agent's attempts at it, in order. A failure that is corrected
may be followed by another attempt ("once the agent gets the request right"). -/
structure Exchange where
  request  : Request
  attempts : List Attempt
  deriving Repr

/-! ### Preparation and sessions -/

/-- "any problems that could interfere with training" -/
structure Problem where
  description    : String
  couldInterfere : Bool
  dealtWith      : Bool
  deriving Repr

/-- "Before each session, the user must check that the agent is rested, that any problems that
could interfere with training have been dealt with, and that the user understands the request
they plan to teach." -/
structure Preparation where
  /-- the user performed the check -/
  checked         : Bool
  agentRested     : Bool
  problems        : List Problem
  /-- ids of the requests the user understands -/
  userUnderstands : List Nat
  deriving Repr

/-- A session is either begun or, per Rule 3, postponed. -/
inductive Status
  | begun
  | postponed
  deriving Repr, DecidableEq

/-- "A session is a single, continuous period of training." -/
structure Session where
  /-- "the request they plan to teach" -/
  planned     : List Request
  preparation : Preparation
  status      : Status
  exchanges   : List Exchange
  deriving Repr

/-- "The agent is ready when the preparation described in Rule 3 is complete." -/
def Session.Ready (s : Session) : Prop :=
  s.preparation.agentRested = true ∧
  (∀ p ∈ s.preparation.problems, p.couldInterfere = true → p.dealtWith = true) ∧
  (∀ r ∈ s.planned, r.id ∈ s.preparation.userUnderstands)

instance (s : Session) : Decidable s.Ready :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Facts the manual takes for granted: requests happen "during a session" (a postponed
session has none), each request is one the user planned, and each has at least one attempt. -/
def Session.WellFormed (s : Session) : Prop :=
  (s.status = .postponed → s.exchanges.isEmpty = true) ∧
  (∀ e ∈ s.exchanges, e.attempts.isEmpty = false ∧ e.request.id ∈ s.planned.map (·.id))

instance (s : Session) : Decidable s.WellFormed :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## §3 The three rules -/

/-- **Rule 1: Reward every success.**
"If the agent carries out a request correctly, the user must reward it. Give the reward
immediately after the success. This applies after a correction too: once the agent gets the
request right, the user must reward it." -/
def Rule1 (std : Standards) (s : Session) : Prop :=
  ∀ e ∈ s.exchanges, ∀ a ∈ e.attempts, a.outcome = .success → a.RewardedImmediately std

instance (std : Standards) (s : Session) : Decidable (Rule1 std s) :=
  inferInstanceAs (Decidable (∀ e ∈ s.exchanges, ∀ a ∈ e.attempts, _ → _))

/-- **Rule 2: Correct every failure.**
"If the agent does not carry out a request correctly, the user must give a correction. Correct
the agent right away, while the request is still fresh." -/
def Rule2 (std : Standards) (s : Session) : Prop :=
  ∀ e ∈ s.exchanges, ∀ a ∈ e.attempts, a.outcome = .failure → a.CorrectedWhileFresh std

instance (std : Standards) (s : Session) : Decidable (Rule2 std s) :=
  inferInstanceAs (Decidable (∀ e ∈ s.exchanges, ∀ a ∈ e.attempts, _ → _))

/-- **Rule 3: Train only when ready.** It has three sentences, kept as three clauses. -/
structure Rule3 (s : Session) : Prop where
  /-- "The user must not begin a session unless the agent is ready." -/
  noStartUnlessReady : s.status = .begun → s.Ready
  /-- "Before each session, the user must check that ..." -/
  mustCheck          : s.preparation.checked = true
  /-- "If the agent is not ready, postpone the session." -/
  postponeIfNotReady : ¬ s.Ready → s.status = .postponed

instance (s : Session) : Decidable (Rule3 s) :=
  decidable_of_iff
    ((s.status = .begun → s.Ready) ∧ s.preparation.checked = true ∧ (¬ s.Ready → s.status = .postponed))
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- A session follows the manual. -/
structure Compliant (std : Standards) (s : Session) : Prop where
  wellFormed : s.WellFormed
  rule1      : Rule1 std s
  rule2      : Rule2 std s
  rule3      : Rule3 s

instance (std : Standards) (s : Session) : Decidable (Compliant std s) :=
  decidable_of_iff (s.WellFormed ∧ Rule1 std s ∧ Rule2 std s ∧ Rule3 s)
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-! ## §4 How the rules fit together — theorems -/

/-- "every request ends in either a success or a failure, so exactly one of Rule 1 or Rule 2
applies to it." -/
theorem exactly_one_rule_triggers (a : Attempt) :
    (a.outcome = .success ∨ a.outcome = .failure) ∧
    ¬ (a.outcome = .success ∧ a.outcome = .failure) := by
  cases a with
  | mk o r d =>
    cases o
    · exact ⟨.inl rfl, fun ⟨_, h⟩ => nomatch h⟩
    · exact ⟨.inr rfl, fun ⟨h, _⟩ => nomatch h⟩

/-- The first two sentences of Rule 3 say the same thing (given that a session is either begun
or postponed): one is the contrapositive of the other. -/
theorem rule3_clauses_equivalent (s : Session) :
    (s.status = .begun → s.Ready) ↔ (¬ s.Ready → s.status = .postponed) := by
  constructor
  · intro h hn
    cases hs : s.status with
    | begun     => exact absurd (h hs) hn
    | postponed => rfl
  · intro h hb
    by_cases hr : s.Ready
    · exact hr
    · have := h hr
      rw [hb] at this
      cases this

/-- "Rule 3 is checked once, before every session. After that, ..." — in a compliant session,
if any request was made at all, the agent was ready. -/
theorem requests_imply_ready (std : Standards) (s : Session)
    (h : Compliant std s) (hne : s.exchanges ≠ []) : s.Ready := by
  cases hs : s.status with
  | begun     => exact h.rule3.noStartUnlessReady hs
  | postponed => exact absurd (eq_nil_of_isEmpty (h.wellFormed.1 hs)) hne

/-- A postponed (well-formed) session satisfies Rules 1 and 2 trivially: there are no requests. -/
theorem postponed_rules_vacuous (std : Standards) (s : Session)
    (hw : s.WellFormed) (hp : s.status = .postponed) : Rule1 std s ∧ Rule2 std s := by
  have hx := eq_nil_of_isEmpty (hw.1 hp)
  constructor <;> (intro e he; rw [hx] at he; cases he)

/-- "This applies after a correction too: once the agent gets the request right, the user must
reward it." Rule 1 already covers this case; the theorem makes it explicit. -/
theorem reward_after_correction (std : Standards) (s : Session) (h1 : Rule1 std s)
    {e : Exchange} (he : e ∈ s.exchanges) {pre post : List Attempt} {a b : Attempt}
    (hab : e.attempts = pre ++ a :: b :: post)
    (_corrected : a.CorrectedWhileFresh std) (hsucc : b.outcome = .success) :
    b.RewardedImmediately std :=
  h1 e he b (hab ▸ mem_append_cons_cons pre post a b) hsucc

/-- A compliant user never punishes: every attempt gets a genuine reward or correction, and
neither is a punishment. -/
theorem compliant_never_punishes (std : Standards) (s : Session) (h : Compliant std s) :
    ∀ e ∈ s.exchanges, ∀ a ∈ e.attempts, a.response.isPunishment = false := by
  intro e he a ha
  cases ho : a.outcome with
  | success => exact reward_not_punishment _ (h.rule1 e he a ha ho).1
  | failure => exact correction_not_punishment _ (h.rule2 e he a ha ho).1

/-- In a compliant session every attempt gets exactly the response its outcome calls for. -/
theorem compliant_response_matches_outcome (std : Standards) (s : Session) (h : Compliant std s) :
    ∀ e ∈ s.exchanges, ∀ a ∈ e.attempts,
      (a.outcome = .success ↔ a.response.isGenuineReward = true) := by
  intro e he a ha
  constructor
  · intro ho; exact (h.rule1 e he a ha ho).1
  · intro hr
    cases ho : a.outcome with
    | success => rfl
    | failure =>
      exact absurd ⟨hr, (h.rule2 e he a ha ho).1⟩ (reward_correction_exclusive a.response)

/-! ## Diagnostics -/

/-- Which parts of the manual a session breaks. -/
def Session.violations (std : Standards) (s : Session) : List String :=
  (if decide s.WellFormed then [] else ["not well-formed"]) ++
  (if decide (Rule1 std s) then [] else ["Rule 1: a success was not rewarded immediately"]) ++
  (if decide (Rule2 std s) then [] else ["Rule 2: a failure was not corrected while fresh"]) ++
  (if decide (s.status = .begun → s.Ready) then []
    else ["Rule 3: session begun although the agent was not ready"]) ++
  (if s.preparation.checked then [] else ["Rule 3: the user did not check before the session"]) ++
  (if decide (¬ s.Ready → s.status = .postponed) then []
    else ["Rule 3: the agent was not ready but the session was not postponed"])

/-! ## Examples -/

/-- One reading of the vague timing words. -/
def std : Standards := { immediately := 1, freshFor := 2 }

def sit   : Request := ⟨1, "sit"⟩
def fetch : Request := ⟨2, "fetch"⟩

def calmNo   : CorrectionAct := ⟨"calm 'no', then show the right move", true, true, true, true⟩
def shouting : CorrectionAct := ⟨"shouting", false, false, true, false⟩

def goodPrep : Preparation :=
  { checked := true, agentRested := true,
    problems := [⟨"noisy room", true, true⟩, ⟨"rain outside", false, false⟩],
    userUnderstands := [1, 2] }

/-- Sit succeeds and is rewarded; fetch fails, is corrected, then succeeds and is rewarded. -/
def goodSession : Session where
  planned     := [sit, fetch]
  preparation := goodPrep
  status      := .begun
  exchanges   :=
    [ ⟨sit,   [⟨.success, .reward praise, 0⟩]⟩,
      ⟨fetch, [⟨.failure, .correction calmNo, 1⟩, ⟨.success, .reward praise, 0⟩]⟩ ]

/-- The reward comes too late. -/
def lateReward : Session := { goodSession with
  exchanges := [⟨sit, [⟨.success, .reward praise, 5⟩]⟩] }

/-- Shouting is not brief, calm, or guiding, so it is not a correction. -/
def harshReply : Session := { goodSession with
  exchanges := [⟨fetch, [⟨.failure, .correction shouting, 0⟩]⟩] }

/-- A failure answered with punishment. -/
def punished : Session := { goodSession with
  exchanges := [⟨fetch, [⟨.failure, .punishment "scolding", 0⟩]⟩] }

/-- The agent is tired, but the session goes ahead anyway. -/
def tiredStart : Session := { goodSession with
  preparation := { goodPrep with agentRested := false } }

/-- The agent is tired, so the session is postponed: compliant. -/
def tiredPostponed : Session := { tiredStart with status := .postponed, exchanges := [] }

example : Compliant std goodSession    := by decide
example : Compliant std tiredPostponed := by decide
example : ¬ Compliant std lateReward   := by decide
example : ¬ Compliant std harshReply   := by decide
example : ¬ Compliant std punished     := by decide
example : ¬ Compliant std tiredStart   := by decide

/-- Under a laxer reading of "immediately", the late reward is fine. -/
example : Compliant { std with immediately := 5 } lateReward := by decide

#eval [("goodSession", goodSession), ("lateReward", lateReward), ("harshReply", harshReply),
       ("punished", punished), ("tiredStart", tiredStart), ("tiredPostponed", tiredPostponed)].map
  fun (n, s) => (n, s.violations std)

end Small1.Lang
