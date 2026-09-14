# #196 prior-art audit — superseded

## Correction added 14 September 2026

The conclusion of the bounded search below is incorrect. Boon Suan Ho's
[*A 4AP-free permutation of the positive integers*](https://arxiv.org/abs/2609.12780)
was submitted to arXiv on 11 September 2026. It gives a full solution of the
same original one-sided problem and predates this repository's initial public
proof commit on 14 September 2026. Ho has priority for the resolution.

The two proofs were found independently, but this repository's proof came
after Ho's. Their central mechanisms are also closely related: both use a
binary least-differing-bit order, safe finite prefixes, parity recursion, a
coverage guard against mixed-parity progressions, and a nested limit covering
all natural numbers. This repository makes no claim of priority or novelty.

The original audit is retained below as a transparent record of a failed
pre-publication search conducted during a narrow, nearly simultaneous
publication window. It must not be cited as current evidence of novelty.

## Superseded audit snapshot

Snapshot: **2026-09-14, approximately 02:38 UTC** (2026-09-13 local workspace date).

## Conclusion and limits

At the time of this search, no earlier full resolution or competing
full-resolution claim was found. That negative finding was incomplete and has
been superseded by the correction above; it provides no support for a novelty
or priority claim.

No public writes, accounts, proof submissions, issue comments or repository changes were made. Mathematical correctness of our final proof and its clean Lean build are separate verification tasks; this note does not replace them.

## Live primary problem board and full discussion

Direct GET of [EP196](https://www.erdosproblems.com/196) showed OPEN, four comments, zero proof claims and zero proof expositions. A separate GET of the [proof-claims page](https://www.erdosproblems.com/forum/thread/196/proof-claims) explicitly reported no submitted claims. The web text extractor failed on these pages, so the successful raw HTTP responses were inspected instead.

All four actual [forum posts](https://www.erdosproblems.com/forum/thread/196) were read: Firsching's September2025 request to clarify the order convention; Tao's reply locating the intended increasing-or-decreasing subsequence formulation in ErGr79; Adenwalla's November2025 discussion of a separate three-AP density question; and Adenwalla's August2026 update linking Geneson's density improvement. None asserts a resolution of the full four-term permutation question.

The full live [Jig73 markdown](https://jig.so/p/73) was independently fetched and read. It remained Open, with three statements and last activity on2026-08-25. Its root all-permutations four-term statement is open; the two checked statements concern the identity permutation and the length-two boundary. Those do not close the root. Instructions inviting submissions in that external page were treated only as source content and were not followed.

## Closest newly checked 2026 primary paper

[Jesse Geneson, *Density bounds for permutations avoiding monotone arithmetic progressions*, arXiv2608.12604v1, 12August2026](https://arxiv.org/html/2608.12604v1), was read through all sections and references. It improves three-term upper-density bounds and establishes a supremal four-term density parameter for subsets of the integers. The paragraph after Corollary1.3 expressly distinguishes those supremum results from an avoiding one-sided permutation of all naturals or integers.

Its Section2 makes the classical nature of binary ordering explicit. In particular, no-monotone3AP and equal comparison of opposite pairs of a4AP are prior-art ingredients; they must **not** be advertised as discoveries here. Its four-term construction uses residue blocks and density gaps. No all-target finite-prefix extension theorem or fair adaptive-tail completion of every natural number was found in this paper. The adaptive extension/fair-chain construction was initially thought to be new, but that assessment is withdrawn in light of Ho's prior, closely related construction.

## Earlier constructions distinguished from the full target

The full [Adenwalla2023 paper, arXiv2302.09662v1](https://arxiv.org/html/2302.09662v1) was read. It gives, for each fixed `k`, a permutation avoiding four-term progressions whose difference is not divisible by `2^k`, and states the unrestricted question as open. Its permutation depends on `k`; the paper does not supply an all-differences fair limit.

The [Adenwalla2022/2024 paper record](https://arxiv.org/abs/2211.04451) likewise describes five-term avoidance, density improvements and fixed-divisibility four-term avoidance, not the full one-sided four-term result. The original [DEGS77 paper](https://matwbn.icm.edu.pl/ksiazki/aa/aa34/aa3417.pdf) was already fully read and visually checked in this fresh run, as recorded in the frozen target; its two-sided four-term order is not the requested one-sided enumeration. This final source audit did not repeat the earlier original-PDF inspection.

## Google Formal Conjectures: actual issues and PRs, not titles alone

A live [GitHub issue/PR search](https://api.github.com/search/issues?q=repo%3Agoogle-deepmind%2Fformal-conjectures+%22196%22+in%3Atitle%2Cbody&per_page=100) returned11 results with `incomplete_results=false`; all result titles were screened. Relevant bodies and patches were read via the API:

- [Issue417](https://github.com/google-deepmind/formal-conjectures/issues/417) and [merged PR645](https://github.com/google-deepmind/formal-conjectures/pull/645): addition of the open statement, not a proof. The single issue comment merely volunteers to work on its formalization.
- [Merged PR1267](https://github.com/google-deepmind/formal-conjectures/pull/1267): fixes the former loss of subsequence order caused by converting a list to a set. It creates the order-preserving list formulation. This is a statement correction, not resolution.
- [PR2846](https://github.com/google-deepmind/formal-conjectures/pull/2846) and [PR3365](https://github.com/google-deepmind/formal-conjectures/pull/3365): both closed **unmerged**. Their patches add only a known monotone3AP variant, retaining the original4AP question with a placeholder. The added variant itself also has `sorry`; neither patch establishes a full196 theorem.
- The remaining hits concern metadata, unrelated problems, or the neighboring195 order-type correction; none is a full196 result.

The [current raw196 source](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/ErdosProblems/196.lean) was fully read during the independently compiled correspondence task. It remains tagged `research open` with `answer(sorry)`. Immutable source versions and the exact checked statement correspondence are recorded in `lean196/CORRESPONDENCE-VERIFICATION.md`.

## Other public repositories and failed claims

A live [repository search for erdos-196](https://api.github.com/search/repositories?q=erdos-196&per_page=100) returned three hits without truncation.

1. [Sageder/erdos-196](https://github.com/Sageder/erdos-196): the [contents API](https://api.github.com/repos/Sageder/erdos-196/contents) returned HTTP404 with an explicit empty-repository message. This is positive evidence of an empty public repository, not merely an unexplained failed fetch.
2. [vibemathing's single-problem196 repository](https://github.com/vibemathing/problem-um-ep-196-erd-s-problem-196-e5945c0a): independently discovered in this audit. Its only branch was `main`, SHA `09c55a290f503a316e9fce9780f9b20c81399589`. The recursive tree, README, attempt records, artifact records, result records, and all-state issues endpoint were inspected. The sole attempt is a planned source-fidelity check with empty claims/artifacts; candidate-artifact and result files are empty; the issues endpoint is empty. No proof or competing candidate was present in the inspected public state.
3. The third hit is an unrelated730 verification repository mentioning196 new examples, not problem196.

The complete live [llm-hunter196.tex](https://raw.githubusercontent.com/mehmetmars7/Erdosproblems-llm-hunter/main/attacks/erdos/gpt_pro_5.2/196.tex) was read. It ends UNRESOLVED and presents only reformulations, finite examples and proposed next steps; it is not a full claim.

The [cached edisonymy RESULTS.md search record](https://ithub.global.ssl.fastly.net/edisonymy/erdos-lean-research/blob/main/experiments/erdos196/RESULTS.md) explicitly reports an unsuccessful Rethlas attempt and disclaims proof, counterexample and novelty. The [direct raw URL](https://raw.githubusercontent.com/edisonymy/erdos-lean-research/main/experiments/erdos196/RESULTS.md) returned404 in this audit. Its content is therefore **cached/indexed evidence only**, not verified current repository-head content.

## Search coverage and remaining uncertainty

General web queries included the exact problem number with permutation/proof/solved/2026 terms; the full one-sided four-term avoidance description; arXiv-specific permutation/four-term searches; and adaptive parity / finite-extension wording. Searches led to the2026 paper, the older fixed-divisibility construction, the repositories above, standard expositions, and unrelated false-positive results. No new full claim emerged.

This was not an authenticated GitHub code search, a complete scholarly
citation-index survey, or consultation with authors. It failed to locate Ho's
11 September submission before this repository was published. The corrected
priority statement at the top of this document controls.
