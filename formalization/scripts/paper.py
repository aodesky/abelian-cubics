"""Read the manuscript's labelled statements without ever writing to the TeX file.

This parser covers the manuscript's theorem and display environments, not arbitrary
TeX expansion. Revision wrappers remain part of the statement being reviewed.
"""

from dataclasses import dataclass
import re


RESULT_KINDS = {"theorem", "lemma", "proposition", "corollary", "example"}
MATH_KINDS = RESULT_KINDS | {"equation", "align", "multline", "gather", "rem", "remark"}
LABEL = re.compile(r"\\label\{([^{}]+)\}")
SECTION_LABEL = re.compile(
    r"\\(?:sub)*section\*?(?:\[[^\]]*\])?"
    r"\{(?:[^{}]|\{[^{}]*\})*\}\s*\\label\{([^{}]+)\}"
)
BLOCK = re.compile(
    r"\\begin\{(" + "|".join(sorted(MATH_KINDS)) + r")\*?\}"
    r".*?\\end\{\1\*?\}",
    re.DOTALL,
)


@dataclass(frozen=True)
class Statement:
    label: str
    kind: str
    line: int
    text: str


def strip_comments(source: str) -> str:
    """Strip unescaped percent comments, preserving newlines and escaped percents."""
    lines = []
    for line in source.splitlines(keepends=True):
        for i, char in enumerate(line):
            if char != "%":
                continue
            backslashes = 0
            j = i - 1
            while j >= 0 and line[j] == "\\":
                backslashes += 1
                j -= 1
            if backslashes % 2 == 0:
                line = line[:i] + ("\n" if line.endswith("\n") else "")
                break
        lines.append(line)
    return "".join(lines)


def normalize(text: str) -> str:
    return " ".join(text.split())


def statements(source: str) -> dict[str, Statement]:
    source = strip_comments(source)
    section_labels = {m[1] for m in SECTION_LABEL.finditer(source)}
    blocks = list(BLOCK.finditer(source))
    # Find displays inside theorem statements too; the outer regex consumes them.
    for outer in tuple(blocks):
        if outer[1] in RESULT_KINDS | {"rem", "remark"}:
            body_start = source.index("}", outer.start()) + 1
            blocks.extend(BLOCK.finditer(source, body_start, outer.end()))
    result = {}
    seen = set()
    labelled_blocks = set()
    for label in LABEL.finditer(source):
        key = label[1]
        if key in seen:
            raise ValueError(f"Duplicate active TeX label: {key}")
        seen.add(key)
        containing = [b for b in blocks if b.start() <= label.start() < b.end()]
        if not containing:
            # Section and figure labels are not mathematical result targets.
            if key.startswith(("sec:", "fig:")) or key in section_labels:
                continue
            raise ValueError(f"Unrecognized environment for mathematical label: {key}")
        block = min(containing, key=lambda b: b.end() - b.start())
        labelled_blocks.add((block.start(), block.end()))
        result[key] = Statement(
            key, block[1], source.count("\n", 0, label.start()) + 1,
            normalize(block[0]),
        )
    for block in blocks:
        if block[1] in RESULT_KINDS and (block.start(), block.end()) not in labelled_blocks:
            line = source.count("\n", 0, block.start()) + 1
            raise ValueError(f"Unlabelled {block[1]} at line {line}")
    return result
