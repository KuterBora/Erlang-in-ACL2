Here are some thoughts about rewriting and :use hints.

Generally, you shouldn't need lots of :use hints.  Having lots of such
hints is common for "intermediate" users of ACL2.  The typical progression
kind of goes like this:
  1.  Start using ACL2.  It seems almost magical how it can set up
        induction proofs and in many cases discharge all of the
        subgoals and be done.  Rewriting and induction are the two
        main proof techniques used by ACL2, and at this beginner
        phase, the rewriter can be viewed as a "black box", or, perhaps.
        almost magical.
  2.  As your proofs get more complicated, you find that a proof fails
        on a subgoal.  No problem, think about the subgoal, state a
        lemma, prove the lemma and try again.  But sometimes, ACL2
        doesn't use the "obvious" lemma.  You find that you can add
        a :use hint to get the lemma instance that you need.  BTW,
        make sure that the rule you are :use'ing is disabled first.
        I'll add some remarks about that below.
          It's kind of natural to use :use hints:
            a.  They worked for simple proofs.
            b.  If you've used another proof assistant, you may be used
                  to the idea that you need to guide the proof assistant
                  one baby step at a time through the proof.  That's why
                  they are called "proof assistants", and why users of
                  proof assistants such as Roq or Lean want to call ACL2
                  a theorem prover.
                    ACL2 really does try to be a theorem prover.  If
                  the lemmas are set-up "right", then the next theorem
                  is often proven just by proving it.  OK, in reality,
                  the next theorem often fails on some subgoal.  From
                  that failed subgoal, you can figure out which lemma
                  was stated in a not-so-helpful way.  Clean that up,
                  and then the proof just goes through.  Better yet,
                  you've fixed the problem for all future theorems you
                  try to prove.  If you keep your ACL2 theorems
                  hint-minimal, you'll find that you're doing less
                  work in the long run.
  3.  Learn to write rewrite rules that match the terms you want to
        have simplified without needing additional hints.  This is
        really learning to use the rewriter as an execution engine
        for rewrite rules, and your set of rewrite rules is a "program"
        for the rewriters.

How do you get rid of :use hints (and maybe other hints as well)?
Often the answer is in the :use hint itself.  First, let's look at
what the rewriter does.  With a bit of simplification, rewrite rules
are of the form:
  (implies hyps (equal lhs rhs))
where hyps stands for hypotheses; lhs stands for "left-hand-side" of the equality,
and rhs stands for "right-hand-side" of the equality.  Of course, equality is
commutative; so, (implies hyps (equal lhs rhs)) is logically equivalent to
(implies hyps (equal rhs lhs)), that's because the rewriter looks for instances
of lhs that it can rewrite to rhs, but not the other way around.  Rules should
be defined so that rhs is is some sense simpler than lhs.  If done systematically,
this often leads to rewriting terms into some kind of canonical form, and that
can make theorem proving much easier to automate.
  How does the rewriter apply these rules?  Let's look at rewriting a single
term.  ACL2 won't rewrite variables; so if a term is a candidate for rewriting,
it must be of the form
  (fn arg0 arg1 ...)
For this to match a rewrite rule, fn must be the same in this term and in the
lhs for the rule.  Thus, the rewriter only needs to consider rules that rewrite
terms of the form (fn arg0 arg1 ...).  Then the rewriter recursively tries to
match arg0, arg1, ... of lhs to the same in term being rewriten.  For each
such subterm either lhs can have:
  *  a free variable -- in which case the rewriter matches the variable to
       the subterm from the goal.  If the variable has already been bound,
       the rewriter checks to see if the current subterm from the goal
       matches the previously determined binding.  If so, the matching
       process continues, otherwise it fails;
  *  a function call, i.e. (fun2 b0 b1 ...)
      in which case the rewriter checks that the subterm from the goal
      is also a call of fun2, and then recursively continues trying to
      match b0, b1, ...
  *  a constant -- the rewriter checks that the subterm has a constant
      that is equal to the one in the lhs.
If the match is successful, then the rewriter attempts to discharge hyps.
This is done by further rewriting which is called backchaining.

I've skipped some details, most importantly the "preprocessing" step that
construct the type-alist, propagates forward-chaining, congruence, and linear
rules, and does simple inferences related to monadic functions (i.e. the
"tau" system).

Another issue is "free" warnings.  This means that there is a variable
in hyps or rhs that doesn't appear in lhs.  When the rewriter finds a
match for lhs, it has no idea what do use for that variable.  Generally,
this is an undesirable situation, but sometimes its unavoidable.  In the
latter case, you can add
  :match-free :all
to the :rule-classes part of the theorem.  This should be done sparingly
or it will cause ACL2 to run *much* slower.  See the discussion of :match-free
in :doc free-variables.

The most common reason that a rule doesn't match is because there term that
you want to rewrite doesn't match the lhs of the rule.  Instead, there is
some "obvious" way to construct the matching term, but ACL2 doesn't even
try.  This is what you were showing me on Monday when you had a rule of
the form:
  (implies hyps
    (equal (apply-k val (append klst1 klst2))
           (apply-k (apply-k val klst1) klst2)))
(or something similar) and wanted to make an inference about
  (apply-k val (cons k1 klst2))
You know that
  (equal (cons k1 klst2)
         (append (cons k1 nil) klst2))
but ACL2 doesn't do that construction for you.
So, you use a :use hint to introduce the hypothesis
  (implies hyps
    (equal (apply-k val (append (cons k1 nil) klst2))
           (apply-k (apply-k val (cons k1 nil)) klst2)))
and let other rewrite rules simplify this to
  (implies hyps
    (equal (apply-k val (cons k1 klst2))
           (apply-k (apply-k val (cons k1 nil)) klst2)))
and presumably some simplification for (apply-k val (cons k1 nil)).

I believe that apply-k take a list-of-continuations as it's argument.
Presumably, you have a function that computes the result of processing
a singleton continuation.  I'll call this apply-k1, but you probably
have another name for it.  Then, the hypothesis introduced by the :use
hint simplifies to
  (implies hyps
    (equal (apply-k val (cons k1 klst2))
           (apply-k (apply-k1 val k1) klst2)))
Better yet, I'll guess that the proof of apply-k-of-append uses a lemma about
  (apply-k val (cons (k1 klst2)))
I'll call this lemma apply-k-of-cons.  Having this lemma makes the proof
of apply-k-of-append 'trivial' (for some value of 'trivial').
Great.  Make sure that both apply-k-of-append and apply-k-of-cons are
defined and enabled for the rewriter.  Now, you shouldn't need the first
:use hint that we looked at.

But yikes, there are so many :use hints.  Indeed.  OTOH, my guess is that
we can apply this approach and get rid of most of them.

There will be a few, annoying ones left.  Sometimes, the rewriter is unable
to discharge one of the or more of hyps.  That can be because there is some
hypothesis that isn't guaranteed to hold (oops) or because showing that the
hypothesis holds requires more reasoning that simple rewriting.  Another
lemma may be needed.  Or you may find a way to strengthen the original
theorem by proving it with weaker hypotheses.  Often, we state theorems
with the "obvious" hypotheses.  When we see the theorem fail to be applied,
we realize that we had an unneccessary hypothesis, or a hypothesis that is
stronger than needed.  Restating the theorem in a more general way makes
subsequent proofs easier.  Of course, these cases aren't resolved with a
:use hint, but they are a common case of a rewrite rule not firing when
expected.

Next, there are rules that really need to be expressed as congruences,
see :doc defcong.  Congruences are helpful when you have equivalence classes.
For example, x1 and x2 might not satisfy (equal x1 x2) but there might be some
weaker equivalence relation that they do satisfy.  If for some function, f,
you can prove
  (implies (my-equiv x1 x2)
           (equal (f args x1 more-args) (f args x2 more-args)))
then you have a congruence rule.  Congruence rules can be more general than
this example I wrote above.  You can have two equivalence relations, equiv1
and equiv2.  If you can prove
  (implies (equiv1 x1 x2)
           (equiv2 (f args x1 more-args) (f args x2 more-args)))
then you have a congruence rule.  Congruence rules can be very handy.
You'll probably get rid of most of your :use hints and the come to Chris
or me with an example where there doesn't seem to be a way to express the
rewrite rule that you need.  If this turns out to be a congruence rule,
then congratulations!!!  You'll now have an example where the motivation
is clear, and you'll probably go back and add a bunch of congruence rules
to your books and find that they greatly reduce the number of hints that
you need.

I'm hoping that you'll go through the :use hints that you showed me on
Monday, and find that many can be eliminated just by making sure that
the rule is stated in a way where lhs can match the term you want to
have rewritten.  There should be a much smaller set of hints remaining,
and I won't be surprised if we spot some congruence rules just waiting
to be proven.

One last word about :use.  Do you get the ACL2 warning about :use of
an enabled rule?  This should (imho) be an error, not a warning.  See
:doc set-warnings-as-errors.  In particular, I really like:
  (set-warnings-as-errors t '("Use") state)
Sadly, fty violates it, so you need a bit of care.  I may fix the fty
issue and propose it as a fix to the fty books.
  Why is it bad to :use an enabled rule?  As noted above, :use
introduces a new hypothesis of the form
  (implies hyps (equal lhs rhs))
where hyps, lhs, and rhs are instantiated by the bindings you provided
in the :use hint.  Clearly, the instantiated lhs matches the lhs of
the enabled rule!  This means that the rewriter can rewrite the instantiated
rule to t, and the hypothesis of t is discarded.  In other words, if
you :use an enabled rule, it will have the desired effect if the rewriter
propagates the consequences of this new hypothesis to the rest of the
goal *before* obliterating the hypothesis.  Otherwise, the hint has no
effect.  Such proofs are very brittle.  Don't do that.  Use
  (set-warnings-as-errors t '("Use") state)