#!/usr/bin/env python3
"""Insert dbgTrace branch markers into the Lean transaction model (scratch copy only).

Every branch arm (if/else arms, match arms, `let pat := e | alt` alternatives) gets a marker
"COV <id>". In do-blocks a statement arm gets a marker statement before its first element; an
expression arm is wrapped as `(dbgTrace "COV n" fun _ => <expr>)`; a pure multi-line arm is
wrapped as one block. A header ending in `:= do` gets an "entry" marker, reported separately.
"""
import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
subdirs = ["XRPL/Model/Vault", "XRPL/Model/Lending", "XRPL/Model/Lending1_1"]
files = []
for d in subdirs:
    files += sorted((root / d).rglob("*.lean"))

manifest = []
counter = 0


def marker_id(path, lineno, kind, text):
    global counter
    counter += 1
    manifest.append(
        {"id": counter, "file": str(path.relative_to(root)), "line": lineno, "kind": kind, "text": text.strip()}
    )
    return counter


def indent_of(s):
    return len(s) - len(s.lstrip(" "))


STMT_START = re.compile(r"^(return\b|let\b|for\b|if\b|match\b|unless\b|throw\b|throwThe\b|\w[\w'.]*\s*←|\w[\w'.]*\s*:=)")
NESTED_HDR = re.compile(r"^(if\b|match\b|unless\b|for\b).*\b(then|with|do|=>)$")
REASSIGN = re.compile(r"^\w[\w'.]*\s*:=")
KEYWORD_RETURN = re.compile(r"^return\b")
DEF_RE = re.compile(r"^(private |protected |noncomputable |@\[[^\]]*\] )*(def|instance|theorem|abbrev)\b")


def split_comment(expr):
    k = expr.find("  --")
    if k == -1:
        k = expr.find(" --")
    if k != -1:
        return expr[:k].rstrip(), expr[k:]
    return expr, ""


def wrap_expr(expr, mid):
    expr, comment = split_comment(expr)
    return f'(dbgTrace "COV {mid}" fun _ => {expr})' + comment


def stmt_marker(indent, mid):
    return " " * indent + f'dbgTrace "COV {mid}" fun _ => pure ()'


def split_top_level_else(s):
    depth = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and s.startswith(" else ", i):
            return s[:i], s[i + 6 :]
        i += 1
    return s, None


def enclosing_is_do(src, i):
    d = i
    while d >= 0 and not (indent_of(src[d]) == 0 and DEF_RE.match(src[d])):
        d -= 1
    if d < 0:
        return False
    k = d
    while k < len(src):
        t = src[k].rstrip()
        if t.endswith(":= do"):
            return True
        if t.endswith(":=") or t.endswith("where"):
            return False
        k += 1
    return False


def is_header(stripped):
    return stripped.endswith("then") or stripped == "else" or stripped.endswith("=>") or stripped.endswith(" do") or stripped == "do"


def oneliner(path, line, lineno):
    """Instrument a line holding one or more complete arms; None if it holds none."""
    stripped = line.strip()
    ind = indent_of(line)
    if stripped.startswith("--") or not stripped or is_header(stripped):
        return None

    # if / else-if with the arm(s) on the same line
    m_if = re.match(r"^(\s*)((?:else )?if\b.*?\bthen) (.+)$", line)
    if m_if:
        pre, arm = m_if.group(2), m_if.group(3)
        then_arm, else_arm = split_top_level_else(arm)
        mid1 = marker_id(path, lineno, "then", then_arm)
        out = []
        if KEYWORD_RETURN.match(then_arm.strip()) or REASSIGN.match(then_arm.strip()):
            out.append(" " * ind + pre)
            out.append(stmt_marker(ind + 2, mid1))
            out.append(" " * (ind + 2) + then_arm.strip())
            if else_arm is not None:
                mid2 = marker_id(path, lineno, "else", else_arm)
                out.append(" " * ind + "else")
                out.append(stmt_marker(ind + 2, mid2))
                out.append(" " * (ind + 2) + else_arm.strip())
        else:
            new = " " * ind + pre + " " + wrap_expr(then_arm.strip(), mid1)
            if else_arm is not None:
                mid2 = marker_id(path, lineno, "else", else_arm)
                new += " else " + wrap_expr(else_arm.strip(), mid2)
            out.append(new)
        return out

    # inline `... := if c then A else B`
    m_inl = re.match(r"^(\s*)(.*?:= )if (.*?) then (.+)$", line)
    if m_inl and " else " in m_inl.group(4):
        then_arm, else_arm = split_top_level_else(m_inl.group(4))
        if else_arm is not None and not then_arm.strip().endswith("do"):
            mid1 = marker_id(path, lineno, "then", then_arm)
            mid2 = marker_id(path, lineno, "else", else_arm)
            tail = ""
            e = else_arm.rstrip()
            while e and e[-1] in "})],":
                tail = e[-1] + tail
                e = e[:-1].rstrip()
            return [
                " " * ind + m_inl.group(2) + "if " + m_inl.group(3) + " then " + wrap_expr(then_arm.strip(), mid1)
                + " else " + wrap_expr(e.strip(), mid2) + (" " + tail if tail else "")
            ]

    # `else <expr>`
    m_else = re.match(r"^(\s*)else (.+)$", line)
    if m_else and not stripped.startswith("else if"):
        arm = m_else.group(2)
        mid = marker_id(path, lineno, "else", arm)
        if KEYWORD_RETURN.match(arm.strip()) or REASSIGN.match(arm.strip()):
            return [" " * ind + "else", stmt_marker(ind + 2, mid), " " * (ind + 2) + arm.strip()]
        return [" " * ind + "else " + wrap_expr(arm.strip(), mid)]

    # match arm `| pat => expr`
    m_arm = re.match(r"^(\s*)(\| .*? =>) (.+)$", line)
    if m_arm:
        arm = m_arm.group(3)
        mid = marker_id(path, lineno, "match", arm)
        if KEYWORD_RETURN.match(arm.strip()) or REASSIGN.match(arm.strip()):
            return [" " * ind + m_arm.group(2), stmt_marker(ind + 2, mid), " " * (ind + 2) + arm.strip()]
        return [" " * ind + m_arm.group(2) + " " + wrap_expr(arm.strip(), mid)]

    # standalone `| return v` / `| throw e` alternative of a `let pat ← e` early exit
    m_alt2 = re.match(r"^(\s*)\| (return|throw|pure) (.+)$", line)
    if m_alt2 and "=>" not in line:
        alt_s = m_alt2.group(2) + " " + m_alt2.group(3)
        mid = marker_id(path, lineno, "alt", alt_s)
        if alt_s.startswith("return"):
            alt_s = "pure " + alt_s[len("return"):].strip()
        return [" " * ind + "| " + wrap_expr(alt_s, mid)]

    # `let pat := e | alt` alternative (an early exit)
    m_alt = re.match(r"^(\s*)(let .*?\s\|\s)(.+)$", line)
    if m_alt and " | " in line and "match" not in line:
        alt_s = m_alt.group(3).strip()
        mid = marker_id(path, lineno, "alt", alt_s)
        if KEYWORD_RETURN.match(alt_s):
            alt_s = "pure " + alt_s[len("return"):].strip()
        return [" " * ind + m_alt.group(2) + wrap_expr(alt_s, mid)]

    return None


def process(path):
    src = path.read_text().split("\n")
    out = []
    i = 0
    n = len(src)
    while i < n:
        line = src[i]
        stripped = line.strip()
        ind = indent_of(line)
        lineno = i + 1

        if stripped.startswith("--") or stripped.startswith("/-") or not stripped:
            out.append(line)
            i += 1
            continue

        if is_header(stripped):
            j_next = i + 1
            while j_next < n and src[j_next].strip().startswith("--"):
                j_next += 1
            nxt = src[j_next] if j_next < n else ""
            nxt_ind = indent_of(nxt) if nxt.strip() else -1
            if not (nxt.strip() and nxt_ind > ind) or (stripped.endswith("=>") and not stripped.startswith("|")):
                out.append(line)
                i += 1
                continue
            kind = "entry" if (stripped.endswith(" do") and ":=" in stripped) else "arm"
            nxt_stripped = nxt.strip()
            first_is_stmt = bool(STMT_START.match(nxt_stripped))
            nxt2 = src[j_next + 1] if j_next + 1 < n else ""
            multi = nxt2.strip() != "" and indent_of(nxt2) == nxt_ind and not nxt2.strip().startswith("--")
            mid = marker_id(path, j_next + 1, kind, nxt_stripped)
            out.append(line)
            out.extend(src[i + 1 : j_next])
            in_do = enclosing_is_do(src, i) or stripped.endswith(" do") or stripped == "do"

            if stripped.endswith(" do") or stripped == "do" or (
                in_do
                and (
                    KEYWORD_RETURN.match(nxt_stripped)
                    or REASSIGN.match(nxt_stripped)
                    or NESTED_HDR.match(nxt_stripped)
                    or (first_is_stmt and (multi or nxt_stripped.startswith("let")))
                )
            ):
                out.append(stmt_marker(nxt_ind, mid))
                i = j_next
                continue

            if not in_do and (multi or nxt_stripped.startswith("let") or NESTED_HDR.match(nxt_stripped)):
                # pure block arm: wrap the whole block, re-indented under the wrapper
                k = j_next
                block = []
                while k < n and (not src[k].strip() or indent_of(src[k]) >= nxt_ind):
                    if not src[k].strip() and (k + 1 >= n or (src[k + 1].strip() and indent_of(src[k + 1]) < nxt_ind)):
                        break
                    block.append(src[k])
                    k += 1
                while block and not block[-1].strip():
                    block.pop()
                    k -= 1
                out.append(" " * nxt_ind + f'(dbgTrace "COV {mid}" fun _ =>')
                inner = []
                for b in block:
                    if b.strip() and not b.strip().startswith("--"):
                        handled = oneliner(path, "  " + b, 0)
                        inner.extend(handled if handled is not None else ["  " + b])
                    else:
                        inner.append("  " + b if b.strip() else b)
                last, comment = split_comment(inner[-1])
                inner[-1] = last + ")" + comment
                out.extend(inner)
                i = k
                continue

            # expression arm, possibly spanning continuation lines: wrap the whole arm
            arm = [src[j_next]]
            k = j_next + 1
            while k < n and src[k].strip() and indent_of(src[k]) > nxt_ind and not src[k].strip().startswith("--"):
                arm.append(src[k])
                k += 1
            arm[0] = " " * nxt_ind + f'(dbgTrace "COV {mid}" fun _ => ' + arm[0].strip()
            last, comment = split_comment(arm[-1])
            arm[-1] = last + ")" + comment
            out.extend(arm)
            i = k
            continue

        handled = oneliner(path, line, lineno)
        if handled is not None:
            out.extend(handled)
        else:
            out.append(line)
        i += 1
    path.write_text("\n".join(out))


for f in files:
    process(f)

(root / "cov-manifest.json").write_text(json.dumps(manifest, indent=1))
kinds = {}
for m in manifest:
    kinds[m["kind"]] = kinds.get(m["kind"], 0) + 1
print(f"instrumented {len(manifest)} markers in {len(files)} files: {kinds}")
