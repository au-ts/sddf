"""
This file provides functions to correctly tokenize the C Copier.
The `preprocessed` function is sound, but the `tokenized` function may need
to be updated in order to tokenize the other Networking components. See
bottom of file for example usage.
"""

from enum import Enum
import regex
from typing import Optional


class AutoNumber(Enum):
    def __new__(cls, *args):
        obj = object.__new__(cls)
        obj._value_ = len(cls.__members__) + 1
        return obj


class PreprocessState(AutoNumber):
    NORMAL = ()
    MULTI_COMMENT = () # multi-line comment
    SINGLE_COMMENT = () # single-line comment
    STRING_LIT = () # string literal
    CHAR_CONST = () # character constant


def preprocessed(source):
    space = " "
    source_chars = list(source)
    
    state = PreprocessState.NORMAL
    i = 0
    while i < len(source):
        char = source[i]    
        if state == PreprocessState.NORMAL:
            if char == "/":
                if source[i + 1] == "*": 
                    state = PreprocessState.MULTI_COMMENT
                    source_chars[i: i + 2] = [space, space]
                    i += 1
                elif source[i + 1] == "/":
                    state = PreprocessState.SINGLE_COMMENT
                    source_chars[i: i + 2] = [space, space]
                    i += 1
            elif char == '"':
                state = PreprocessState.STRING_LIT
            elif char == "'":
                state = PreprocessState.CHAR_CONST
        elif state == PreprocessState.MULTI_COMMENT:
            if char == "*" and source[i + 1] == "/":
                state = PreprocessState.NORMAL
                source_chars[i: i + 2] = [space, space]
                i += 1
            elif char != "\n":
                source_chars[i] = space
        elif state == PreprocessState.SINGLE_COMMENT:
            if char == "\n":
                state = PreprocessState.NORMAL
            else:
                source_chars[i] = space
        elif state == PreprocessState.STRING_LIT:
            if char == '"' and source[i - 1] != "\\":
                state = PreprocessState.NORMAL
        elif state == PreprocessState.CHAR_CONST:
            if char == "'" and source[i - 1] != "\\":
                state = PreprocessState.NORMAL
        i += 1
    
    return "".join(source_chars)


def expr_call(kind):
    return fr"\((?P<{kind}_expr>(?&expr))\)"


token_pattern = regex.compile(fr"""
    (?(DEFINE)(?P<expr>[^()]*(?:\((?&expr)\)[^()]*)*))
    \s+(?:
	    (?P<if_cond>if\s*{expr_call("if")})|
	    (?P<else>else[\s])|
	    (?P<while_cond>while\s*{expr_call("while")})
    )
    |\s*(?:
	    (?P<lbrace>{{)|
	    (?P<rbrace>}})|
	    (?P<sc_suffixed>[^;]*);
    )
""", regex.VERBOSE)


class TokenKind(AutoNumber):
    IF = ()
    EXPR = ()
    ELSE = ()
    WHILE = ()
    LBRACE = () # left brace
    RBRACE = () # right brace
    SC_SUFFIXED = ()


class Token:
    def __init__(self, kind: TokenKind, start_pos: int, literal: Optional[str]):
        self.kind = kind
        self.start_pos = start_pos
        self.literal = literal
        self.line_no = None
    
    def __str__(self):
        return f"Token(kind={self.kind.name}, line_no={self.line_no}, literal={self.literal})"


def tokenized(source):
    tokens = []
    
    for match_object in token_pattern.finditer(source):
        if match_object.group("if_cond") is not None: 
            tokens.extend([
                Token(TokenKind.IF, match_object.start("if_cond"), None),
                Token(TokenKind.EXPR, match_object.start("if_expr"), match_object.group("if_expr"))
            ])
        elif match_object.group("else") is not None:
            tokens.append(Token(TokenKind.ELSE, match_object.start("else"), None))
        elif match_object.group("while_cond") is not None:
            tokens.extend([
                Token(TokenKind.WHILE, match_object.start("while_cond"), None),
                Token(TokenKind.EXPR, match_object.start("while_expr"), match_object.group("while_expr"))
            ])
        elif match_object.group("lbrace") is not None:
            tokens.append(Token(TokenKind.LBRACE, match_object.start("lbrace"), None))
        elif match_object.group("rbrace") is not None:
            tokens.append(Token(TokenKind.RBRACE, match_object.start("rbrace"), None))
        elif match_object.group("sc_suffixed") is not None:
            tokens.append(Token(
                TokenKind.SC_SUFFIXED, match_object.start("sc_suffixed"), match_object.group("sc_suffixed")
            ))
        else:
            raise Exception(f"Unexpected group: {repr(match_object.group())}")

    newline_locations = []
    for i, char in enumerate(source):
        if char == "\n":
            newline_locations.append(i)

    for token in tokens:
        line_no = 1
        while line_no <= len(newline_locations) and token.start_pos > newline_locations[line_no - 1]:
            line_no += 1
        token.line_no = line_no
    
    return tokens


"""
Example usage:

clean_source = preprocessed(source)
tokens = tokenized(clean_source)

for token in tokens:
    print(token)
"""

