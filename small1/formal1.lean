/-
  formal1.lean — small1, formalized from the dataset (small1.json).

  This file takes the JSON at its word: the five atoms, the three rules as
  propositional formulas, and the eight annotated entries with all their
  fields. On top of that it gives
    • a semantics (valuations, evaluation, validity, equivalence),
    • a sound, complete truth-table checker over the five atoms,
    • a conditional deontic reading of each rule (O / F / P) and its violation condition,
    • the JSON's two-level scope (per-session vs per-request atoms) as session records,
    • machine-checked versions of the JSON's "consequences" and of its internal consistency.

  Compare lang1.lean, which formalizes the same rules from the natural-language manual.

  Check with:  lean formal1.lean      (Lean 4, no dependencies)
-/

namespace Small1.Formal

/-! ## Atoms  (small1.json › atoms) -/

inductive Atom
  | session
  | ready
  | success
  | reward
  | correction
  deriving Repr, DecidableEq

/-- small1.json › metadata.logic: "Atoms are evaluated per request (success, reward, correction)
or per session (session, ready)." -/
inductive Scope
  | perSession
  | perRequest
  deriving Repr, DecidableEq

def Atom.scope : Atom → Scope
  | .session | .ready                   => .perSession
  | .success | .reward | .correction    => .perRequest

/-- small1.json › atoms › meaning -/
def Atom.meaning : Atom → String
  | .session    => "the user begins a training session"
  | .ready      => "the agent is ready (all preparation is complete)"
  | .success    => "the agent carries out the current request correctly (¬success = failure)"
  | .reward     => "the user rewards the agent"
  | .correction => "the user gives the agent a correction"

/-- small1.json › atoms › definition_text (verbatim from the manual) -/
def Atom.definitionText : Atom → String
  | .session    => "A session is a single, continuous period of training."
  | .ready      => "The agent is ready when the preparation described in Rule 3 is complete."
  | .success    => "A success is when the agent carries out a request correctly. A failure is when it does not."
  | .reward     => "A reward is any response that the agent values and that makes a success more likely next time, such as praise."
  | .correction => "A correction is a brief, calm response that shows the agent what it did wrong and guides it to the right behaviour. A correction is not a punishment."

def Atom.all : List Atom := [.session, .ready, .success, .reward, .correction]

/-! ## Propositional formulas -/

inductive Formula
  | atom (a : Atom)
  | top
  | bot
  | neg  (φ : Formula)
  | conj (φ ψ : Formula)
  | disj (φ ψ : Formula)
  | imp  (φ ψ : Formula)
  deriving Repr, DecidableEq

notation:max "∼" φ:max => Formula.neg φ
infixl:35 " ⋏ " => Formula.conj
infixl:30 " ⋎ " => Formula.disj
infixr:25 " ⇒ " => Formula.imp

/- Formula versions of the atoms, so rules read like the JSON: `success ⇒ reward`. -/
namespace P
def session    : Formula := .atom .session
def ready      : Formula := .atom .ready
def success    : Formula := .atom .success
def reward     : Formula := .atom .reward
def correction : Formula := .atom .correction
end P

/-- The atoms a formula mentions. -/
def Formula.atoms : Formula → List Atom
  | .atom a   => [a]
  | .top      => []
  | .bot      => []
  | .neg φ    => φ.atoms
  | .conj φ ψ => φ.atoms ++ ψ.atoms
  | .disj φ ψ => φ.atoms ++ ψ.atoms
  | .imp φ ψ  => φ.atoms ++ ψ.atoms

/-- Rendering in the JSON's notation. -/
def Atom.name : Atom → String
  | .session => "session" | .ready => "ready" | .success => "success"
  | .reward => "reward"   | .correction => "correction"

def Formula.render : Formula → String
  | .atom a   => a.name
  | .top      => "⊤"
  | .bot      => "⊥"
  | .neg φ    => "¬" ++ φ.render
  | .conj φ ψ => "(" ++ φ.render ++ " ∧ " ++ ψ.render ++ ")"
  | .disj φ ψ => "(" ++ φ.render ++ " ∨ " ++ ψ.render ++ ")"
  | .imp φ ψ  => φ.render ++ " → " ++ ψ.render

/-! ## Semantics -/

abbrev Valuation := Atom → Bool

def Formula.eval (v : Valuation) : Formula → Bool
  | .atom a   => v a
  | .top      => true
  | .bot      => false
  | .neg φ    => !φ.eval v
  | .conj φ ψ => φ.eval v && ψ.eval v
  | .disj φ ψ => φ.eval v || ψ.eval v
  | .imp φ ψ  => !φ.eval v || ψ.eval v

/-- Evaluation only depends on the values of the atoms. -/
theorem Formula.eval_congr (φ : Formula) {v w : Valuation} (h : ∀ a, v a = w a) :
    φ.eval v = φ.eval w := by
  induction φ with
  | atom a => exact h a
  | top => rfl
  | bot => rfl
  | neg φ ih => simp only [Formula.eval, ih]
  | conj φ ψ ih₁ ih₂ => simp only [Formula.eval, ih₁, ih₂]
  | disj φ ψ ih₁ ih₂ => simp only [Formula.eval, ih₁, ih₂]
  | imp φ ψ ih₁ ih₂ => simp only [Formula.eval, ih₁, ih₂]

/-- A valuation given by five truth values, in the order of `Atom.all`. -/
def Valuation.ofBits (s r su rw c : Bool) : Valuation
  | .session => s | .ready => r | .success => su | .reward => rw | .correction => c

theorem Valuation.ofBits_self (v : Valuation) (a : Atom) :
    v a = Valuation.ofBits (v .session) (v .ready) (v .success) (v .reward) (v .correction) a := by
  cases a <;> rfl

/-! ### Truth tables -/

def forallBool (p : Bool → Bool) : Bool := p true && p false

theorem forallBool_spec {p : Bool → Bool} (h : forallBool p = true) (b : Bool) : p b = true := by
  simp only [forallBool, Bool.and_eq_true] at h
  cases b
  · exact h.2
  · exact h.1

/-- Truth-table validity check over all 32 valuations. -/
def Formula.valid (φ : Formula) : Bool :=
  forallBool fun s => forallBool fun r => forallBool fun su => forallBool fun rw =>
    forallBool fun c => φ.eval (Valuation.ofBits s r su rw c)

/-- The checker is sound: a formula that passes the truth table is true under every valuation. -/
theorem Formula.valid_sound {φ : Formula} (h : φ.valid = true) (v : Valuation) :
    φ.eval v = true := by
  rw [φ.eval_congr (Valuation.ofBits_self v)]
  exact forallBool_spec (forallBool_spec (forallBool_spec (forallBool_spec
    (forallBool_spec h (v .session)) (v .ready)) (v .success)) (v .reward)) (v .correction)

def Formula.iff (φ ψ : Formula) : Formula := (φ ⇒ ψ) ⋏ (ψ ⇒ φ)
def Formula.equivalent (φ ψ : Formula) : Bool := (φ.iff ψ).valid
def Formula.entails (φ ψ : Formula) : Bool := (φ ⇒ ψ).valid
def Formula.satisfiable (φ : Formula) : Bool := !(∼φ).valid

theorem Formula.equivalent_sound {φ ψ : Formula} (h : φ.equivalent ψ = true) (v : Valuation) :
    φ.eval v = ψ.eval v := by
  have := Formula.valid_sound h v
  simp only [Formula.iff, Formula.eval] at this
  cases hφ : φ.eval v <;> cases hψ : ψ.eval v <;> simp_all

theorem Formula.entails_sound {φ ψ : Formula} (h : φ.entails ψ = true) (v : Valuation)
    (hφ : φ.eval v = true) : ψ.eval v = true := by
  have := Formula.valid_sound h v
  simp only [Formula.eval, hφ] at this
  simpa using this

/-! ## Conditional deontic statements -/

/-- `obl φ c`: when `c`, `φ` is obligatory.  `forb φ c`: when `c`, `φ` is forbidden.
`perm φ c`: when `c`, `φ` is permitted. -/
inductive Deontic
  | obl  (φ cond : Formula)
  | forb (φ cond : Formula)
  | perm (φ cond : Formula)
  deriving Repr, DecidableEq

/-- A situation violates a deontic statement when its condition holds and the obligation is
unmet or the forbidden thing happens. Permissions cannot be violated. -/
def Deontic.violated (v : Valuation) : Deontic → Bool
  | .obl φ c  => c.eval v && !φ.eval v
  | .forb φ c => c.eval v && φ.eval v
  | .perm _ _ => false

/-- The material condition that holds exactly when the statement is not violated. -/
def Deontic.toFormula : Deontic → Formula
  | .obl φ c  => c ⇒ φ
  | .forb φ c => c ⇒ ∼φ
  | .perm _ _ => .top

theorem Deontic.violated_iff (d : Deontic) (v : Valuation) :
    d.violated v = !(d.toFormula.eval v) := by
  cases d with
  | obl φ c  =>
    simp only [Deontic.violated, Deontic.toFormula, Formula.eval]
    cases φ.eval v <;> cases c.eval v <;> rfl
  | forb φ c =>
    simp only [Deontic.violated, Deontic.toFormula, Formula.eval]
    cases φ.eval v <;> cases c.eval v <;> rfl
  | perm _ _ => rfl

/-! ## Annotation vocabularies  (the values that occur in small1.json) -/

inductive Party
  | user
  | agent
  deriving Repr, DecidableEq

/-- small1.json › entries › interaction ("user→agent") -/
structure Interaction where
  source : Party
  target : Party
  deriving Repr, DecidableEq

inductive Label
  | Obligation
  | Prohibition
  deriving Repr, DecidableEq

inductive Force
  | required
  | prohibited
  deriving Repr, DecidableEq

/-- Each label has its expected force. -/
def Label.force : Label → Force
  | .Obligation  => .required
  | .Prohibition => .prohibited

inductive Temporal
  | triggered
  | postViolation
  | prospective
  deriving Repr, DecidableEq

inductive Strength
  | absolute
  deriving Repr, DecidableEq

inductive DeonticMarker
  | must
  | mustNot
  | imperative
  deriving Repr, DecidableEq

inductive RuleId
  | R1
  | R2
  | R3
  deriving Repr, DecidableEq

/-! ## Rules  (small1.json › rules) -/

structure Rule where
  id              : RuleId
  name            : String
  heading         : String
  antecedent      : Formula
  consequent      : Formula
  equivalentForm  : Option Formula := none
  scope           : Scope
  scopeText       : String
  label           : Label
  force           : Force
  temporal        : Temporal
  /-- the conditional deontic reading of the rule -/
  deontic         : Deontic
  derivedFrom     : List String
  generalisedFrom : String
  deriving Repr

/-- "formula" in the JSON: antecedent → consequent. -/
def Rule.formula (r : Rule) : Formula := r.antecedent ⇒ r.consequent

def R1 : Rule where
  id              := .R1
  name            := "Reward"
  heading         := "Rule 1: Reward every success."
  antecedent      := P.success
  consequent      := P.reward
  scope           := .perRequest
  scopeText       := "each request within a session"
  label           := .Obligation
  force           := .required
  temporal        := .triggered
  deontic         := .obl P.reward P.success
  derivedFrom     := ["DT020", "DT050", "DT051", "DT066", "DT067", "DT068", "DT069",
                      "DT082", "DT086", "DT087", "DT092", "DT106", "DT107"]
  generalisedFrom := "reward the dog with praise / food / petting whenever it performs the desired behaviour, including after it complies following a correction"

def R2 : Rule where
  id              := .R2
  name            := "Correction"
  heading         := "Rule 2: Correct every failure."
  antecedent      := ∼P.success
  consequent      := P.correction
  scope           := .perRequest
  scopeText       := "each request within a session"
  label           := .Obligation
  force           := .required
  temporal        := .postViolation
  deontic         := .obl P.correction (∼P.success)
  derivedFrom     := ["DT048", "DT051", "DT062", "DT071", "DT072", "DT078", "DT080",
                      "DT085", "DT096", "DT100", "DT102", "DT103", "DT104"]
  generalisedFrom := "when the dog does not comply, correct it promptly, calmly and minimally (never punish)"

def R3 : Rule where
  id              := .R3
  name            := "Readiness"
  heading         := "Rule 3: Train only when ready."
  antecedent      := P.session
  consequent      := P.ready
  equivalentForm  := some (∼P.ready ⇒ ∼P.session)
  scope           := .perSession
  scopeText       := "each session"
  label           := .Prohibition
  force           := .prohibited
  temporal        := .prospective
  deontic         := .forb P.session (∼P.ready)
  derivedFrom     := ["DT015", "DT016", "DT021", "DT024", "DT028", "DT029", "DT031",
                      "DT033", "DT041", "DT042"]
  generalisedFrom := "before training, make sure the dog is rested and healthy and the owner understands the exercise; otherwise do not train"

def rules : List Rule := [R1, R2, R3]

def RuleId.rule : RuleId → Rule
  | .R1 => Formal.R1
  | .R2 => Formal.R2
  | .R3 => Formal.R3

/-! ## Entries  (small1.json › entries) -/

structure Entry where
  id              : String
  /-- verbatim sentence from small1_training_manual.txt -/
  text            : String
  rule            : RuleId
  role            : String
  label           : Label
  force           : Force
  formula         : Formula
  bearer          : Party := .user
  regulated       : Party
  interaction     : Interaction := ⟨.user, .agent⟩
  /-- verbatim condition phrase -/
  condition       : String
  temporal        : Temporal
  strength        : Strength := .absolute
  defeasible      : Bool := false
  deonticMarkers  : List DeonticMarker
  temporalMarkers : List String := []
  deriving Repr

def S01 : Entry where
  id := "S01"
  text := "If the agent carries out a request correctly, the user must reward it."
  rule := .R1
  role := "core statement"
  label := .Obligation
  force := .required
  formula := P.success ⇒ P.reward
  regulated := .agent
  condition := "If the agent carries out a request correctly"
  temporal := .triggered
  deonticMarkers := [.must]

def S02 : Entry where
  id := "S02"
  text := "Give the reward immediately after the success."
  rule := .R1
  role := "timing"
  label := .Obligation
  force := .required
  formula := P.success ⇒ P.reward
  regulated := .agent
  condition := "after the success"
  temporal := .triggered
  deonticMarkers := [.imperative]
  temporalMarkers := ["immediately"]

def S03 : Entry where
  id := "S03"
  text := "This applies after a correction too: once the agent gets the request right, the user must reward it."
  rule := .R1
  role := "scope extension: also covers success that follows a correction"
  label := .Obligation
  force := .required
  formula := P.success ⇒ P.reward
  regulated := .agent
  condition := "once the agent gets the request right"
  temporal := .postViolation
  deonticMarkers := [.must]
  temporalMarkers := ["once"]

def S04 : Entry where
  id := "S04"
  text := "If the agent does not carry out a request correctly, the user must give a correction."
  rule := .R2
  role := "core statement"
  label := .Obligation
  force := .required
  formula := ∼P.success ⇒ P.correction
  regulated := .agent
  condition := "If the agent does not carry out a request correctly"
  temporal := .postViolation
  deonticMarkers := [.must]

def S05 : Entry where
  id := "S05"
  text := "Correct the agent right away, while the request is still fresh."
  rule := .R2
  role := "timing"
  label := .Obligation
  force := .required
  formula := ∼P.success ⇒ P.correction
  regulated := .agent
  condition := "while the request is still fresh"
  temporal := .postViolation
  deonticMarkers := [.imperative]
  temporalMarkers := ["right away", "while"]

def S06 : Entry where
  id := "S06"
  text := "The user must not begin a session unless the agent is ready."
  rule := .R3
  role := "core statement"
  label := .Prohibition
  force := .prohibited
  formula := P.session ⇒ P.ready
  regulated := .user
  condition := "unless the agent is ready"
  temporal := .prospective
  deonticMarkers := [.mustNot]

def S07 : Entry where
  id := "S07"
  text := "Before each session, the user must check that the agent is rested, that any problems that could interfere with training have been dealt with, and that the user understands the request they plan to teach."
  rule := .R3
  role := "content of 'ready': the preparation checklist"
  label := .Obligation
  force := .required
  formula := P.session ⇒ P.ready
  regulated := .user
  condition := "Before each session"
  temporal := .prospective
  deonticMarkers := [.must]
  temporalMarkers := ["Before", "each"]

def S08 : Entry where
  id := "S08"
  text := "If the agent is not ready, postpone the session."
  rule := .R3
  role := "contrapositive / what to do instead"
  label := .Prohibition
  force := .prohibited
  formula := ∼P.ready ⇒ ∼P.session
  regulated := .user
  condition := "If the agent is not ready"
  temporal := .prospective
  deonticMarkers := [.imperative]

def entries : List Entry := [S01, S02, S03, S04, S05, S06, S07, S08]

/-! ## Checks on the dataset itself -/

/-- Every rule's deontic reading has exactly the rule's formula as its non-violation condition. -/
theorem rules_deontic_match :
    rules.all (fun r => r.deontic.toFormula.equivalent r.formula) = true := by decide

/-- R3's alternative form ("¬ready → ¬session") is equivalent to its main formula. -/
theorem R3_equivalentForm : (∼P.ready ⇒ ∼P.session).equivalent R3.formula = true := by decide

/-- Every entry's formula is equivalent to the formula of the rule it is filed under
(S08 is stated in contrapositive form). -/
theorem entries_match_rules :
    entries.all (fun e => e.formula.equivalent e.rule.rule.formula) = true := by decide

/-- Rules' labels and forces agree. -/
theorem rules_label_force : rules.all (fun r => r.label.force == r.force) = true := by decide

/-- Entries' labels and forces agree (S07 is an Obligation inside the Prohibition rule R3: it
obliges the check that makes the prohibition followable). -/
theorem entries_label_force : entries.all (fun e => e.label.force == e.force) = true := by decide

/-- Every entry is borne by the user, and is about a user→agent interaction. -/
theorem entries_borne_by_user :
    entries.all (fun e => e.bearer == .user && e.interaction == ⟨.user, .agent⟩) = true := by decide

/-- R1 and R2 regulate the agent's training; R3 regulates the user's own conduct. -/
theorem entries_regulated :
    entries.all (fun e => e.regulated == (if e.rule == .R3 then .user else .agent)) = true := by
  decide

/-- Each rule mentions only atoms of its own scope (R1, R2: per request; R3: per session). -/
theorem rules_respect_scope :
    rules.all (fun r => r.formula.atoms.all (fun a => a.scope == r.scope)) = true := by decide

/-- How many dog-training entries each rule generalises (13, 13, 10). -/
theorem derivedFrom_counts : rules.map (fun r => r.derivedFrom.length) = [13, 13, 10] := rfl

/-- All eight entries are absolute and not defeasible. -/
theorem entries_absolute :
    entries.all (fun e => e.strength == .absolute && !e.defeasible) = true := by decide

/-! ## The JSON's consequences -/

/-- The three rules together. -/
def allRules : Formula := R1.formula ⋏ R2.formula ⋏ R3.formula

/-- metadata.consequences[0]: "For every request exactly one of R1 or R2 is triggered, since
success ∨ ¬success." -/
theorem exactly_one_triggered_valid :
    ((R1.antecedent ⋎ R2.antecedent) ⋏ ∼(R1.antecedent ⋏ R2.antecedent)).valid = true := by decide

theorem exactly_one_triggered (v : Valuation) :
    (R1.antecedent.eval v || R2.antecedent.eval v) = true ∧
    (R1.antecedent.eval v && R2.antecedent.eval v) = false := by
  have := Formula.valid_sound exactly_one_triggered_valid v
  simp only [Formula.eval, Bool.and_eq_true, Bool.not_eq_true'] at this
  exact ⟨this.1, this.2⟩

/-- The rules are jointly satisfiable. -/
theorem rules_consistent : allRules.satisfiable = true := by decide

/-- Under the rules, every request is answered by a reward or a correction. -/
theorem rules_entail_response : allRules.entails (P.reward ⋎ P.correction) = true := by decide

/-- A gap the formulas leave open: nothing in small1.json forbids rewarding *and* correcting the
same request. (lang1.lean closes it, because there one response is given per attempt.) -/
theorem json_allows_reward_and_correction :
    (allRules ⋏ P.reward ⋏ P.correction).satisfiable = true := by decide

/-- Another gap: the formulas do not forbid correcting a success. -/
theorem json_allows_correcting_success :
    (allRules ⋏ P.success ⋏ P.correction).satisfiable = true := by decide

/-! ## Two-level scope: sessions and their requests -/

/-- Per-session atoms. -/
structure SessionVal where
  session : Bool
  ready   : Bool
  deriving Repr, DecidableEq

/-- Per-request atoms. -/
structure RequestVal where
  success    : Bool
  reward     : Bool
  correction : Bool
  deriving Repr, DecidableEq

/-- The full valuation at one request inside a session. -/
def combine (s : SessionVal) (r : RequestVal) : Valuation :=
  Valuation.ofBits s.session s.ready r.success r.reward r.correction

/-- One session with all its requests. -/
structure SessionRecord where
  sv       : SessionVal
  requests : List RequestVal
  deriving Repr

/-- Requests only occur inside a session that was begun. -/
def SessionRecord.WellFormed (rec : SessionRecord) : Prop :=
  rec.sv.session = false → rec.requests = []

instance (rec : SessionRecord) : Decidable rec.WellFormed :=
  inferInstanceAs (Decidable (_ → _))

/-- A rule holds of a record: per-session rules once, per-request rules at every request. -/
def Rule.holdsIn (r : Rule) (rec : SessionRecord) : Bool :=
  match r.scope with
  | .perSession => r.formula.eval (combine rec.sv ⟨false, false, false⟩)
  | .perRequest => rec.requests.all fun q => r.formula.eval (combine rec.sv q)

def SessionRecord.compliant (rec : SessionRecord) : Bool :=
  decide rec.WellFormed && rules.all (·.holdsIn rec)

/-- metadata.consequences[1]: "R3 is checked before R1/R2 can ever apply, since requests only
occur inside a session." If a well-formed record satisfies R3 and has any request, the agent
was ready. -/
theorem requests_imply_ready (rec : SessionRecord) (hw : rec.WellFormed)
    (h3 : R3.holdsIn rec = true) (hne : rec.requests ≠ []) : rec.sv.ready = true := by
  obtain ⟨⟨s, r⟩, qs⟩ := rec
  simp only [Rule.holdsIn, R3, Rule.formula, P.session, P.ready, Formula.eval, combine,
    Valuation.ofBits] at h3
  cases s with
  | false => exact absurd (hw rfl) hne
  | true  => simpa using h3

/-- Which rules a record breaks. -/
def SessionRecord.violations (rec : SessionRecord) : List RuleId :=
  (rules.filter (fun r => !r.holdsIn rec)).map (·.id)

/-! ## Examples -/

def good : SessionRecord :=
  ⟨⟨true, true⟩, [⟨true, true, false⟩, ⟨false, false, true⟩, ⟨true, true, false⟩]⟩

def unrewarded : SessionRecord := ⟨⟨true, true⟩, [⟨true, false, false⟩]⟩

def uncorrected : SessionRecord := ⟨⟨true, true⟩, [⟨false, false, false⟩]⟩

def notReady : SessionRecord := ⟨⟨true, false⟩, [⟨true, true, false⟩]⟩

def postponed : SessionRecord := ⟨⟨false, false⟩, []⟩

example : good.compliant = true        := by decide
example : postponed.compliant = true   := by decide
example : unrewarded.compliant = false := by decide
example : notReady.violations = [.R3]  := by decide

#eval rules.map fun r => (r.id, r.formula.render, r.label, r.force)

#eval entries.map fun e => (e.id, e.rule, e.formula.render)

#eval [("good", good), ("unrewarded", unrewarded), ("uncorrected", uncorrected),
       ("notReady", notReady), ("postponed", postponed)].map
  fun (n, rec) => (n, rec.compliant, rec.violations)

end Small1.Formal
