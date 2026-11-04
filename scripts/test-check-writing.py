#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Tests for the advisory writing checker, `scripts/check-writing.py`."""

from __future__ import annotations

from contextlib import ExitStack
import errno
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


WRITING = load("check_writing", "check-writing.py")


def findings(text: str, path: str = "doc.md") -> list[str]:
    blocks = WRITING.file_blocks(path, text)
    return sorted({item.rule for item in WRITING.check_blocks(blocks)})


class WritingRuleTests(unittest.TestCase):
    def test_vocabulary_is_parsed(self) -> None:
        general, history = WRITING.avoid_words()
        self.assertIn("utilize", general)
        self.assertIn("e.g.", general)
        self.assertIn("no longer", history)
        self.assertNotIn("now", history)
        self.assertNotIn("new", history)

    def test_sentence_length(self) -> None:
        long_sentence = " ".join(["word"] * 26) + "."
        self.assertEqual(findings(long_sentence), ["S1"])
        self.assertEqual(findings(" ".join(["word"] * 25) + "."), [])
        self.assertEqual(findings("1. " + " ".join(["word"] * 21) + "."), ["S1"])
        self.assertEqual(findings("- " + " ".join(["word"] * 21) + "."), [])

    def test_text_in_parentheses_is_a_separate_sentence(self) -> None:
        inner = " ".join(["word"] * 40)
        self.assertEqual(findings(f"The bound holds ({inner})."), ["S1"])
        self.assertEqual(findings(f"The bound holds (see ({inner}))."), ["S1"])
        self.assertEqual(findings("The bound holds (for each code)."), [])

    def test_one_word_elements(self) -> None:
        sentence = ("The bound `Code.dist_le_of_mem (h : x ∈ C)` and $\\delta \\le 1 - \\sqrt{\\rho}$ "
                    "from [BCIKS20, Theorem 1.2] and [the page](https://example.org/a.b) hold "
                    "(for every code that this page lists) here.")
        self.assertEqual(findings(sentence), [])
        counted = WRITING.mask(sentence, collapse_parentheses=True)
        self.assertEqual(WRITING.word_count(counted), 13)

    def test_sentence_can_start_with_a_lowercase_filename(self) -> None:
        text = " ".join(["word"] * 20) + ". pr-scope.py " + " ".join(["word"] * 20) + "."
        self.assertEqual(findings(text), [])
        self.assertEqual(len(WRITING.sentences(text)), 2)

    def test_license_text_is_exempt_but_later_prose_is_checked(self) -> None:
        legal = "## Licensing\n\nEnsure these terms; do not change them.\n"
        self.assertEqual(findings(legal, "CONTRIBUTING.md"), [])
        nested = legal + "\n### Conditions\n\nWe utilize these terms.\n"
        self.assertEqual(findings(nested, "CONTRIBUTING.md"), [])
        resumed = nested + "\n## Next steps\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(resumed, "CONTRIBUTING.md"), ["W1"])
        self.assertEqual(findings("Ensure these terms; do not change them.", "LICENSE.md"), [])
        fenced = "```md\n## License\n```\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(fenced), ["W1"])

    def test_mathematical_terms_are_not_blanket_vocabulary_bans(self) -> None:
        for text in ["The following are equivalent.", "Every valid transcript has a witness.",
                     "The space is simply connected.", "This functor is essentially surjective.",
                     "Complete the pull request template."]:
            self.assertNotIn("W1", findings(text), text)

    def test_paragraph_length(self) -> None:
        self.assertEqual(findings(" ".join(["One sentence."] * 7)), ["P2"])
        self.assertEqual(findings(" ".join(["One sentence."] * 6)), [])

    def test_punctuation(self) -> None:
        self.assertEqual(findings("The code is linear; it is also cyclic."), ["U1"])
        self.assertEqual(findings("The code is linear — it is also cyclic."), ["U2"])
        self.assertEqual(findings("The Reed–Solomon code has rate 1–2 in this range."), [])
        self.assertEqual(findings("Write `a; b` in Lean."), [])
        blocks = WRITING.file_blocks("doc.md", "A short clause; another clause.")
        self.assertEqual([item.excerpt for item in WRITING.check_blocks(blocks)],
                         ["A short clause; another clause."])

    def test_definition_separator_is_not_a_clause_join(self) -> None:
        for dash in ["—", "–", "--"]:
            for term in ["`Δ₀(u, v)`", "``Δ₀(u, v)``", "$\\delta$", "**Relative distance**"]:
                with self.subTest(dash=dash, term=term):
                    self.assertEqual(findings(f"- {term} {dash} `hammingDist u v`."), [])
        self.assertNotIn("U2", findings("- `Λ(C, δ, f)` and `Λ(C, δ)` — write `Code.Lambda C δ`."))
        self.assertEqual(findings("- `Gadget/` (§2.1) — the gadget matrix."), [])
        self.assertEqual(findings("- `EvalSplit.lean` (§4, Eq. (12)) — the matrix split."), [])

    def test_definition_description_is_still_checked(self) -> None:
        self.assertEqual(findings("- `δ` — We utilize the lemma."), ["W1"])
        self.assertEqual(findings("- `δ` — relative distance — it is bounded."), ["U2"])
        self.assertEqual(findings("- `δ` — relative distance.\n  The code is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("- `C` is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("- `C` (§2.1) is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("| Term | Description |\n|---|---|\n| `C` is linear — it is cyclic. | Bound |"), ["U2"])

    def test_words(self) -> None:
        self.assertEqual(findings("Use a ring, e.g. the integers."), ["W7"])
        self.assertEqual(findings("We utilize the lemma."), ["W1"])
        self.assertEqual(findings("Set up the build."), ["W6"])
        self.assertEqual(findings("The word ends in a vowel."), [])
        self.assertEqual(findings("Don't run the build."), ["S5"])
        self.assertEqual(findings("The prover's message is short."), [])

    def test_verbs(self) -> None:
        self.assertEqual(findings("The lemma has changed."), ["V1"])
        self.assertEqual(findings("The verifier is rejecting the proof string."), ["V1"])
        self.assertEqual(findings("The polynomials have bounded degree."), [])
        self.assertEqual(findings("The witness is missing."), [])
        self.assertNotIn("V2", findings("Using the lemma, we bound the error."))
        self.assertEqual(findings("Folding halves the length of the word."), [])
        self.assertEqual(findings("During a merge, the base is the merge base."), [])
        self.assertEqual(findings("The request may have failed."), [])

    def test_bare_this(self) -> None:
        self.assertEqual(findings("The bound is tight. This is the main result."), ["S7"])
        self.assertEqual(findings("The bound is tight. This lemma is the main result."), [])

    def test_history_words_apply_to_library_text_only(self) -> None:
        for path in ["docs/agents/page.md", "AGENTS.md"]:
            self.assertEqual(findings("The lemma is no longer needed.", path), ["C3"], path)
        self.assertEqual(findings("-- The lemma is no longer needed.\n", "VCVio/A.lean"), ["C3"])
        for path in ["body.md", "docs/reading/record.md", "docs/design/plan.md"]:
            self.assertEqual(findings("The lemma is no longer needed.", path), [], path)
        self.assertEqual(findings("The new code is now linear.", "docs/agents/page.md"), [])

    def test_security_properties_are_not_progressive_forms(self) -> None:
        self.assertEqual(findings("The commitment scheme is hiding and binding."), [])
        self.assertEqual(findings("The adversary is querying the oracle."), ["V1"])

    def test_cryptographic_terms_are_not_vocabulary_findings(self) -> None:
        for text in ["The simulator answers each query.", "The reduction is tight.",
                     "A negligible function is eventually below every inverse polynomial.",
                     "The forking lemma bounds the extraction probability."]:
            self.assertEqual(findings(text), [], text)

    def test_exempt_text(self) -> None:
        text = ("Avoid \"e.g.; it's robust\" in prose.\n\n# Heading; with e.g. a dash — here\n\n"
                "```\nlet x := 1; e.g.\n```\n\n<!-- e.g.; utilize -->\n")
        self.assertEqual(findings(text), [])

    def test_table_cells_and_header(self) -> None:
        text = "| Rule; header | Use |\n|---|---|\n| One cell; two | Fine. |\n"
        self.assertEqual(findings(text), ["U1"])


class LeanExtractionTests(unittest.TestCase):
    def test_doc_comments_and_line_numbers(self) -> None:
        source = ('/-! # Title\n\nThe module; with a problem. -/\n'
                  'def f : Nat := 1 -- a trailing comment; also a problem\n'
                  'def s : String := "-- not a comment; ok"\n'
                  '/-- The definition utilizes `x; y`. -/\n'
                  'theorem t : True := trivial\n')
        blocks = WRITING.lean_blocks("A.lean", source)
        lines = {block.line: block.text for block in blocks}
        self.assertIn(3, lines)
        self.assertIn(4, lines)
        self.assertIn(6, lines)
        self.assertNotIn(5, lines)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(3, "U1"), (4, "U1"), (6, "W1")})

    def test_character_literals_do_not_start_strings(self) -> None:
        source = ("def quote : Char := '\"'\n"
                  "def escaped : Char := '\\''\n"
                  "def x' : Nat := 1\n"
                  "/-- The definition utilizes a quote. -/\n"
                  "def y : Nat := 2\n")
        blocks = WRITING.lean_blocks("A.lean", source)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(4, "W1")})


class ChangedLineTests(unittest.TestCase):
    def setUp(self) -> None:
        # Keep fixture Git commands and checker reads independent of the contributor's setup.
        contexts = ExitStack()
        self.addCleanup(contexts.close)
        template = contexts.enter_context(tempfile.TemporaryDirectory())
        environment = {key: value for key, value in os.environ.items()
                       if not key.upper().startswith("GIT_")}
        environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_SYSTEM=os.devnull,
                           GIT_CONFIG_GLOBAL=os.devnull, GIT_TEMPLATE_DIR=template)
        contexts.enter_context(mock.patch.dict(os.environ, environment, clear=True))

    def test_only_changed_blocks_are_checked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)

            def run(*args: str) -> None:
                subprocess.run(["git", "-c", f"core.hooksPath={os.devnull}",
                                "-c", "commit.gpgSign=false", *args],
                               cwd=root, check=True, capture_output=True)

            run("init", "-q", "-b", "main")
            run("config", "user.email", "test@example.org")
            run("config", "user.name", "Test")
            (root / "page.md").write_text("Old text; with a semicolon.\n\nA clean line.\n")
            run("add", "page.md")
            run("commit", "-q", "-m", "base")
            run("checkout", "-q", "-b", "topic")
            (root / "page.md").write_text(
                "Old text; with a semicolon.\n\nA clean line.\n\nNew text; also bad.\n")
            (root / "untracked.md").write_text("Untracked; ignored.\n")
            with mock.patch.object(WRITING, "ROOT", root):
                blocks = WRITING.changed_blocks("main")
            self.assertEqual([block.line for block in blocks], [5])

    def test_unchanged_symbolic_alias_does_not_repeat_the_target(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)

            def run(*args: str) -> None:
                subprocess.run(["git", "-c", f"core.hooksPath={os.devnull}",
                                "-c", "commit.gpgSign=false", *args],
                               cwd=root, check=True, capture_output=True)

            run("init", "-q", "-b", "main")
            run("config", "user.email", "test@example.org")
            run("config", "user.name", "Test")
            (root / "AGENTS.md").write_text("A clean line.\n")
            (root / "CLAUDE.md").symlink_to("AGENTS.md")
            run("add", "AGENTS.md", "CLAUDE.md")
            run("commit", "-q", "-m", "base")
            run("checkout", "-q", "-b", "topic")
            (root / "AGENTS.md").write_text("A clean line.\n\nNew text; also bad.\n")
            run("add", "AGENTS.md")
            run("commit", "-q", "-m", "topic")
            with mock.patch.object(WRITING, "ROOT", root):
                blocks = WRITING.changed_blocks("main")
            self.assertEqual([(block.path, block.line) for block in blocks], [("AGENTS.md", 3)])


class CommandLineTests(unittest.TestCase):
    def run_main(self, *args: str, stdin: str = "") -> tuple[int, str]:
        output = io.StringIO()
        with mock.patch("sys.stdin", io.StringIO(stdin)), mock.patch("sys.stdout", output):
            code = WRITING.main(["check-writing.py", *args])
        return code, output.getvalue()

    def test_findings_are_advisory(self) -> None:
        code, output = self.run_main("--stdin", "body", stdin="Don't run the build.\n")
        self.assertEqual(code, 0)
        self.assertIn("[S5]", output)

    def test_github_output_uses_warnings_and_escapes_data(self) -> None:
        code, output = self.run_main("--stdin", "body", "--github",
                                     stdin="We utilize 100% of it; twice.\n")
        self.assertEqual(code, 0)
        self.assertIn("::warning title=Writing U1::", output)
        self.assertIn("100%25", output)
        self.assertNotIn("::error", output)

    def test_files_are_checked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "page.md"
            path.write_text("A clean line.\n")
            code, output = self.run_main(str(path))
        self.assertEqual(code, 0)
        self.assertIn("No writing findings.", output)

    def test_symlink_directory_and_loops_are_advisory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "directory").mkdir()
            (root / "directory.md").symlink_to("directory", target_is_directory=True)
            (root / "loop.md").symlink_to("loop.md")
            (root / "a.md").symlink_to("b.md")
            (root / "b.md").symlink_to("a.md")
            good = root / "good.md"
            good.write_text("Actual prose; checked.\n")
            for name in ["directory.md", "loop.md", "a.md"]:
                with self.subTest(name=name):
                    code, output = self.run_main(str(root / name), str(good))
                    self.assertEqual(code, 0)
                    self.assertIn("[Input]", output)
                    self.assertIn("symlink", output)
                    self.assertIn("[U1]", output)

    def test_other_input_errors_still_fail(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path in [root, root / "missing.md"]:
                with self.subTest(path=path), mock.patch("sys.stderr", io.StringIO()):
                    with self.assertRaises(SystemExit) as result:
                        self.run_main(str(path))
                    self.assertEqual(result.exception.code, 2)
            target = root / "target.md"
            target.write_text("Clean prose.\n")
            original = Path.read_text

            def denied(path: Path, *args, **kwargs):
                if path == target:
                    raise PermissionError(errno.EACCES, "permission denied")
                return original(path, *args, **kwargs)

            with mock.patch.object(Path, "read_text", denied), \
                    mock.patch("sys.stderr", io.StringIO()) as error:
                with self.assertRaises(SystemExit) as result:
                    self.run_main(str(target))
                self.assertEqual(result.exception.code, 2)
                self.assertIn("permission denied", error.getvalue())

    def test_valid_symlink_is_input_without_a_target_read(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "target.md"
            target.write_text("Clean prose.\n\nLater prose; checked only by its own path.\n")
            link = root / "link.md"
            link.symlink_to("target.md")
            original = Path.read_text

            def no_target_read(path: Path, *args, **kwargs):
                if path in {link, target}:
                    self.fail("A symlink source must not read its target.")
                return original(path, *args, **kwargs)

            with mock.patch.object(Path, "read_text", no_target_read):
                code, output = self.run_main(str(link))
            self.assertEqual(code, 0)
            self.assertIn(f"{link}:1: [Input]", output)
            self.assertNotIn("[U1]", output)

    def test_configuration_error_test_finishes_with_stdin_open(self) -> None:
        command = [sys.executable, "-B", str(Path(__file__).resolve()),
                   "ChangedFileRegressionTests.test_missing_base_and_broken_configuration_are_errors"]
        with subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT) as process:
            try:
                process.wait(timeout=15)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
                self.fail("The configuration-error test did not finish with stdin open.")
            self.assertFalse(process.stdin.closed)
            output = process.stdout.read().decode()
            self.assertEqual(process.returncode, 0, output)


class V2AdvisoryTests(unittest.TestCase):
    vocabulary = """## Technical -ing nouns

| Term | Technical meaning |
|---|---|
| `encoding`, `folding`, `sampling` | Protocol constructions |
| `gas metering` | Resource accounting |

## Other terms

| `making` | Outside the technical noun table |

## Words to avoid

| Avoid | Use |
|---|---|
| "utilize" | use |
| "no longer" | present fact (rule C3) |
"""

    def test_technical_ing_nouns_are_vocabulary_defined(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'vocabulary.md'
            path.write_text(self.vocabulary)
            self.assertEqual(WRITING.technical_ing_nouns(path),
                             {'encoding', 'folding', 'sampling', 'gas metering'})

    def test_prepositions_do_not_get_a_blanket_suffix_hint(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'vocabulary.md'
            path.write_text(self.vocabulary)
            cases = ['Refer to CONTRIBUTING for docstring rules.',
                     'Before making a change, run the tests.',
                     'Instead of calling the function, use the cached value.',
                     'The bound follows by assuming P.',
                     'After encoding, the message has a fixed length.',
                     'The bound follows from sampling.',
                     'Nothing changes before folding.',
                     'The budget accounts for gas metering.',
                     'Run the tests before\nmaking a change.',
                     'Before using the lemma, the output changes.']
            # This checks hint scope, not whether an actor or mathematical claim is correct.
            for text in cases:
                with self.subTest(text=text):
                    found = WRITING.check_blocks(WRITING.file_blocks('page.md', text), path)
                    self.assertNotIn('V2', [f.rule for f in found])

    def test_intro_hint_requests_actor_review_without_a_rewrite_command(self) -> None:
        text = 'A clean sentence.\nUsing the lemma, the result follows.'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        hints = [f for f in found if f.rule == 'V2']
        self.assertEqual([f.line for f in hints], [2])
        self.assertIn('actor and meaning', hints[0].message)
        self.assertNotIn('finite', hints[0].message)

    def test_limited_conventional_forms_do_not_get_form_hints(self) -> None:
        texts = ['Assuming P, we obtain Q.', 'Using the lemma, we obtain the bound.',
                 'Using the lemma,\nwe obtain the bound.',
                 'Writing f = g, we compare the values.',
                 'Writing `f = g`, the equality follows.']
        # These are lexical exceptions. No hint is not a subject or truth certificate.
        for text in texts:
            with self.subTest(text=text):
                self.assertNotIn('V2', findings(text))

    def test_non_inflections_and_modifiers_do_not_get_suffix_hints(self) -> None:
        for text in ['Bring the lemma into scope, then apply it.',
                     'Morning tests, and evening tests, run.',
                     'Existing files, however, keep their headers.',
                     'Underlying definitions, not names, determine the result.',
                     'Corresponding terms, in this example, have equal values.']:
            with self.subTest(text=text):
                self.assertNotIn('V2', findings(text))

    def test_multiword_terms_do_not_grant_global_word_exemptions(self) -> None:
        vocabulary = self.vocabulary.replace('`encoding`, `folding`, `sampling`',
                                             '`encoding`, `sampling distribution`')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'vocabulary.md'
            path.write_text(vocabulary)
            terms = WRITING.technical_ing_nouns(path)
            self.assertEqual(terms, {'encoding', 'sampling distribution', 'gas metering'})
            self.assertTrue(WRITING.technical_noun_prefix('Sampling\ndistribution, ...', terms))
            self.assertTrue(WRITING.technical_noun_prefix('Gas metering, ...', terms))
            self.assertFalse(WRITING.technical_noun_prefix('Sampling values, ...', terms))
            self.assertFalse(WRITING.technical_noun_prefix('Metering, ...', terms))
            hinted = WRITING.check_blocks(WRITING.file_blocks('page.md',
                                        'Sampling values, the result follows.'), path)
            self.assertIn('V2', [f.rule for f in hinted])

    def test_technical_heading_lookup_and_configuration_errors(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'vocabulary.md'
            for heading in ['# 4. Technical -ing nouns', '### technical -ing nouns ###']:
                path.write_text(self.vocabulary.replace('## Technical -ing nouns', heading))
                self.assertEqual(WRITING.technical_ing_nouns(path),
                                 {'encoding', 'folding', 'sampling', 'gas metering'})
            bad = [self.vocabulary.replace('## Technical -ing nouns', '## Other heading'),
                   self.vocabulary.replace('`encoding`, `folding`, `sampling`', '`encoding`, unquoted'),
                   self.vocabulary.replace('| `encoding`, `folding`, `sampling` | Protocol constructions |\n', '')
                                  .replace('| `gas metering` | Resource accounting |\n', '')]
            for text in bad:
                path.write_text(text)
                with self.subTest(text=text), mock.patch('sys.stdin', io.StringIO('')), \
                        mock.patch('sys.stderr', io.StringIO()):
                    with self.assertRaises(SystemExit) as result:
                        WRITING.main(['check-writing.py', '--stdin', 'body', '--vocabulary', str(path)])
                    self.assertEqual(result.exception.code, 2)


class WritingRegressionTests(unittest.TestCase):
    def test_findings_point_to_the_source_line(self) -> None:
        text = ('The [reference](https://example.org/a(b)) and `x` agree.\n'
                'The quoted "a; b" is code here.\n'
                'The last line; needs a conjunction.\n')
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        item = next(f for f in found if f.rule == 'U1')
        self.assertEqual(item.line, 3)
        self.assertIn('last line;', item.excerpt)
        self.assertNotIn('Code', item.excerpt)

    def test_line_numbers_in_lists_and_lean_comments(self) -> None:
        cases = [('- First line.\n  Second line; needs a conjunction.\n', 'page.md', 2),
                 ('/-! First line.\nSecond line; needs a conjunction.\n-/', 'A.lean', 2),
                 ('-- First line.\n-- Second line; needs a conjunction.\n', 'A.lean', 2)]
        for text, path, line in cases:
            with self.subTest(path=path, text=text):
                found = WRITING.check_blocks(WRITING.file_blocks(path, text))
                self.assertEqual([f.line for f in found if f.rule == 'U1'], [line])

    def test_word_findings_keep_source_spelling_and_line(self) -> None:
        text = 'A clean line with `code`.\nWe utilize the lemma.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([(f.line, f.excerpt) for f in found if f.rule == 'W1'], [(2, 'utilize')])

    def test_parenthetical_length_finding_points_inside_the_parenthesis(self) -> None:
        text = 'A short sentence (\n' + ' '.join(['word'] * 30) + ').'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'S1'], [2])

    def test_possession_is_not_a_perfect_tense(self) -> None:
        for text in ['The code has correlated agreement.', 'The vector has centered norm.',
                     'The vector has squared norm.', 'The variable has expected value zero.',
                     'The tree has left and right children.', 'The polynomials have known degree.',
                     'The graph has labelled edges.']:
            with self.subTest(text=text):
                self.assertNotIn('V1', findings(text))
        self.assertIn('V1', findings('The prover has squared the norm.'))
        self.assertIn('V1', findings('The proof has changed.'))

    def test_technical_predicates_are_not_progressive_actions(self) -> None:
        for text in ['The commitment scheme is hiding and binding.',
                     'The sequence is increasing.', 'The sequence is decreasing.',
                     'The sequence is nondecreasing.', 'The polynomial is vanishing.',
                     'The tree is accepting.', 'The composite is winning.']:
            with self.subTest(text=text):
                self.assertNotIn('V1', findings(text))
        self.assertIn('V1', findings('The verifier is rejecting the message.'))

    def test_noun_and_nonverb_forms_do_not_get_intro_hints(self) -> None:
        for text in ['Nothing, at present.', 'Hamming distance, as defined above, is a metric.',
                     'String concatenation, as usual, is associative.',
                     'Folding is done in blocks, so the bound applies.',
                     'Batching reduces the cost, so use the bound.']:
            with self.subTest(text=text):
                self.assertNotIn('V2', findings(text))
        self.assertIn('V2', findings('Using the lemma, the bound follows.'))

    def test_this_way_has_an_explicit_noun(self) -> None:
        self.assertNotIn('S7', findings('This way, the prover sends one message.'))
        self.assertIn('S7', findings('This is the main result.'))

    def test_definition_separators_allow_links_and_alternatives(self) -> None:
        for term in ['[`File.lean`](path)', '`A` / `B`', '[the term](https://example.org)', '[the term](https://example.org/a(b))',
                     '`A` and [`B`](path)']:
            with self.subTest(term=term):
                self.assertNotIn('U2', findings(f'- {term} — the description.'))
                self.assertIn('U2', findings(f'- {term} — first clause — second clause.'))
        self.assertNotIn('U2', findings('| Term | Meaning |\n|---|---|\n| `A` | — |'))

    def test_latin_abbreviations_have_one_finding(self) -> None:
        for word in ['e.g.', 'i.e.', 'etc.', 'cf.', 'resp.']:
            pattern = WRITING.word_pattern([word])
            blocks = WRITING.file_blocks('page.md', f'Use {word} here.')
            found = [f for b in blocks for f in WRITING.check_block(b, pattern, None)]
            self.assertEqual([f.rule for f in found], ['W7'])

    def test_final_e_verbs_keep_ing_inflections(self) -> None:
        pattern = WRITING.word_pattern(['ensure', 'utilize', 'leverage'])
        for word in ['ensure', 'ensures', 'ensured', 'ensuring', 'utilizing', 'leveraging']:
            self.assertIsNotNone(pattern.fullmatch(word), word)
        self.assertIsNone(pattern.fullmatch('reassuring'))

    def test_fences_use_their_opening_character_and_length(self) -> None:
        for opening, inner in [('~~~~', '```'), ('````', '```'), ('~~~', '```')]:
            text = f'{opening}\n{inner}\nNot prose; ignored.\n{opening}\n\nReal prose; checked.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(6, 'U1')])

    def test_visible_prose_after_comments_and_thematic_breaks(self) -> None:
        for text in ['<!-- comment --> Visible prose; checked.',
                     '---\nVisible prose; checked.\n---', '#1431 has prose; checked.']:
            self.assertIn('U1', findings(text), text)
        self.assertEqual(findings('    Example code; ignored.\n'), [])
        self.assertEqual(findings('---\nstatus: current; metadata\n---\nClean prose.'), [])

    def test_literal_comment_markers_do_not_hide_prose(self) -> None:
        for text in ['The token `<!--` opens a comment.\nReal prose; checked.\n',
                     '```\n<!--\n```\nReal prose; checked.\n',
                     'The token `<!--` is code, as is `-->`.\nReal prose; checked.\n',
                     'The token `some\n<!--\ntext` is literal.\nReal prose; checked.\n',
                     'The text \\<!-- is literal.\nReal prose; checked.\n',
                     'The text \\<!-- literal; --> stays visible.']:
            with self.subTest(text=text):
                self.assertIn('U1', findings(text))
        text = 'A clean line.\n    A bad line; this is paragraph continuation.\n'
        self.assertIn('U1', findings(text))

    def test_indented_list_continuations_remain_prose(self) -> None:
        for text in ['- Outer item.\n\n    - Inner prose; checked.\n',
                     '1. Outer item.\n\n    1. Inner prose; checked.\n',
                     '- Outer item.\n\n    More prose; checked.\n']:
            with self.subTest(text=text):
                self.assertIn('U1', findings(text))

    def test_lean_comment_indentation_does_not_hide_prose(self) -> None:
        cases = [('a.lean', '/-!\n    Indented prose; checked.\n    Next line.\n-/\n', 2),
                 ('a.lean', '/-- First line.\n\n        Indented prose; checked.\n-/\n', 3),
                 ('a.lean', '/-\n    Indented prose; checked.\n-/\n', 2),
                 ('a.lean', '    -- Indented prose; checked.\n', 1),
                 ('a.lean', '/-!\n\n    ```lean\n    Code; ignored.\n    ```\n\n'
                            '    Actual prose; checked.\n-/\n', 7)]
        for path, text, expected_line in cases:
            with self.subTest(text=text):
                found = WRITING.check_blocks(WRITING.file_blocks(path, text))
                self.assertEqual([f.line for f in found if f.rule == 'U1'], [expected_line])
        self.assertEqual(findings('    Code; ignored.\n', 'a.md'), [])

    def test_raw_lean_strings_do_not_create_comments(self) -> None:
        for value in ['r#"a " -- fake; comment"#', 'r"a\\"']:
            text = f'def s := {value}\n-- Real prose; checked.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(2, 'U1')])

    def test_escaped_newlines_in_lean_strings_keep_comment_locations(self) -> None:
        text = 'def s := "a\\\nb"\n-- Actual prose; checked.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
        self.assertEqual([(f.line, f.rule) for f in found], [(3, 'U1')])

    def test_wrapped_technical_phrases_keep_their_meaning(self) -> None:
        for text in ['The code has correlated\nagreement.',
                     'The variable has expected\nvalue zero.']:
            self.assertNotIn('V1', findings(text))

    def test_wrapped_phrasal_and_history_terms_remain_visible(self) -> None:
        self.assertIn('W6', findings('Carry\nout the test.'))
        self.assertIn('C3', findings('The lemma is no\nlonger needed.', 'docs/agents/page.md'))

    def test_wrapped_straight_quotes_are_one_exempt_element(self) -> None:
        text = ('"essentially\nsurjective". Review their meaning. Do not delete them as '
                'isolated words. "Negligible" retains its technical meaning.')
        self.assertEqual(findings(text), [])
        text = 'The text "quoted\nwords; ignored" is literal.\nActual prose; checked.'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'U1'], [3])

    def test_annotation_properties_are_escaped(self) -> None:
        item = WRITING.Finding('a%,line=9::b.md', 2, 'U1', 'message', 'excerpt')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            WRITING.report([item], True, True)
        self.assertIn('file=a%25%2Cline=9%3A%3Ab.md,line=2,', output.getvalue())


class ChangedFileRegressionTests(unittest.TestCase):
    def setUp(self) -> None:
        super().setUp()
        environment = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
        environment.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                           GIT_CONFIG_SYSTEM=os.devnull)
        patcher = mock.patch.dict(os.environ, environment, clear=True)
        patcher.start(); self.addCleanup(patcher.stop)
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        patcher = mock.patch.object(WRITING, 'ROOT', self.root)
        patcher.start(); self.addCleanup(patcher.stop)
        self.git('init', '-q', '-b', 'main', '--template=')
        self.git('config', 'user.email', 'test@example.org')
        self.git('config', 'user.name', 'Test')
        self.git('config', 'commit.gpgsign', 'false')
        self.git('config', 'core.hooksPath', os.devnull)
        self.git('commit', '-q', '--allow-empty', '-m', 'base')
        self.git('checkout', '-q', '-b', 'topic')

    def git(self, *args: str) -> None:
        subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True)

    def test_git_settings_and_quoted_paths_do_not_hide_changes(self) -> None:
        names = ['page.md', 'space name.md', 'café.md', 'quote"name.md', 'back\\slash.md',
                 'line\nbreak.md', ':(glob)nothing.md', ':(literal)foo.md', 'a[1].md', 'a*.md']
        for name in names:
            (self.root / name).write_text('Good line.\nBad line; checked.\n')
        self.git('add', '.')
        for option in ['diff.noprefix', 'diff.mnemonicPrefix', 'core.quotePath']:
            for value in ['true', 'false']:
                with self.subTest(option=option, value=value):
                    self.git('config', option, value)
                    found = WRITING.check_blocks(WRITING.changed_blocks('main'))
                    self.assertEqual({f.path for f in found if f.rule == 'U1'}, set(names))
                    self.assertEqual({f.line for f in found if f.rule == 'U1'}, {2})

    def test_renames_check_only_edited_prose(self) -> None:
        old, new = 'old café.md', 'new name.md'
        text = 'Existing prose; unchanged.\n\nA clean line.\n'
        (self.root/old).write_text(text)
        self.git('add', '.')
        self.git('commit', '-q', '-m', 'base prose')
        self.git('branch', '-f', 'main', 'HEAD')
        self.git('mv', old, new)
        (self.root/new).write_text(text + '\nNew prose; checked.\n')
        self.git('add', '.')
        found = WRITING.check_blocks(WRITING.changed_blocks('main'))
        self.assertEqual([(f.path, f.line) for f in found if f.rule == 'U1'], [(new, 5)])

    def test_inter_hunk_context_does_not_add_unchanged_paragraphs(self) -> None:
        path = self.root / 'page.md'
        text = 'Top source.\n\nUnchanged text; preserved.\n\nBottom source.\n'
        path.write_text(text)
        self.git('add', '.')
        self.git('commit', '-q', '-m', 'base prose')
        self.git('branch', '-f', 'main', 'HEAD')
        path.write_text(text.replace('Top source', 'Top revised')
                       .replace('Bottom source', 'Bottom revised'))
        self.git('config', 'diff.interHunkContext', '5')
        self.assertEqual(WRITING.added_lines('main')['page.md'], {1, 5})
        found = WRITING.check_blocks(WRITING.changed_blocks('main'))
        self.assertNotIn('U1', [f.rule for f in found])

    def test_non_utf8_and_dangling_symlinks_are_advisory(self) -> None:
        (self.root / 'invalid.md').write_bytes(b'Caf\xe9; text.\n')
        (self.root / 'dangling.md').symlink_to('missing-target')
        (self.root / 'good.md').write_text('Actual prose; checked.\n')
        self.git('add', '.')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check-writing.py', '--base', 'main']), 0)
        self.assertIn('not UTF-8', output.getvalue())
        self.assertIn('dangling.md:1: [Input]', output.getvalue())
        self.assertIn('U1', output.getvalue())
        self.assertNotIn('No writing findings', output.getvalue())
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check-writing.py', str(self.root/'dangling.md')]), 0)
        self.assertIn('symlink', output.getvalue())
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check-writing.py', str(self.root/'invalid.md')]), 0)
        self.assertIn('not UTF-8', output.getvalue())

    def test_changed_symlink_does_not_borrow_target_line_numbers(self) -> None:
        target = self.root / 'target.md'
        target.write_text('Clean prose.\n\nLater prose; checked.\n')
        (self.root / 'link.md').symlink_to('target.md')
        self.git('add', '.')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check-writing.py', '--base', 'main']), 0)
        self.assertIn('link.md:1: [Input]', output.getvalue())
        self.assertNotIn('link.md:3:', output.getvalue())
        self.assertIn('target.md:3: [U1]', output.getvalue())

    def test_invalid_byte_stdin_has_an_input_diagnostic(self) -> None:
        environment = dict(os.environ, PYTHONIOENCODING='utf-8:surrogateescape')
        result = subprocess.run([sys.executable, WRITING.__file__, '--stdin', 'body'],
                                input=b'\xff\n', capture_output=True, env=environment)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b'not UTF-8', result.stdout)
        self.assertNotIn(b'No writing findings', result.stdout)

    def test_missing_base_and_broken_configuration_are_errors(self) -> None:
        with mock.patch('sys.stderr', io.StringIO()) as error:
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['check-writing.py', '--base', 'missing-base'])
        self.assertEqual(result.exception.code, 2)
        self.assertIn('git failed', error.getvalue())
        with mock.patch('sys.stderr', io.StringIO()), mock.patch('sys.stdin', io.StringIO('')):
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['check-writing.py', '--stdin', 'body', '--vocabulary',
                              str(self.root/'missing-vocabulary')])
        self.assertEqual(result.exception.code, 2)



if __name__ == "__main__":
    unittest.main()
