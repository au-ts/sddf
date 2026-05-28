"""
This file contains a partially complete implementation of a C language 
control flow graph (CFG) generator.

If you decide to generate a CFG, then you should make changes to the
`CParser` class, noting the bug documented below (and that more may exist
since the implementation is untested). If you decide to generate an abstract
syntax tree (AST), then most code can be removed, with the exception of the
helper methods in the `CParser` class, which may be helpful.
"""

from typing import Optional, Self

from .cfg import CFG, Edge
from .tokenizer import Token, TokenKind, preprocessed, tokenized


NO_OP = "NO_OP"


class SubgraphInfo:
    """
    For CFG generation. Can remove if building AST.
    """
    def __init__(self, parent_graph: CFG):
        self.parent_graph = parent_graph
        self.entry: Optional[int] = None
        self.out_edges: list[tuple[Edge, int]] = []
    
    def connect_next(self, next_node: Self):
        for edge_kind, node in self.out_edges:
            self.parent_graph.connect_nodes(node, next_node.entry, edge_kind)

    def add_oedge(self, edge: Edge, node: int) -> None:
        self.out_edges.append((edge, node))


# NOTE: The `CParser` class is functionally incorrect. In particular, the `comp_stmt` method is based on an outdated grammar.
class CParser:
    """
    If building CFG, fix `comp_stmt`, complete `if_stmt` and potentially add
    other methods. If building AST, remove all but the helper methods.
    """
    def __init__(self, tokens: list[Token]):
        self.tokens = tokens
        self.curr_ind = 0
        self._cfg = CFG()
    
    def while_loop(self) -> SubgraphInfo:
        """while_loop -> 'WHILE' 'EXPR' COMP_STMT"""
        while_info = SubgraphInfo(self._cfg)
        self.match(TokenKind.WHILE)
        self.match(TokenKind.EXPR)
        while_info.entry = self._cfg.new_node(self.prev_token().literal)
        comp_info = self.comp_stmt()
        self._cfg.connect_nodes(while_info.entry, comp_info.entry, Edge.TRUE)
        comp_info.connect_next(while_info)
        while_info.add_oedge(Edge.FALSE, while_info.entry)
        return while_info
    
    def comp_stmt(self) -> SubgraphInfo:
        """comp_stmt -> 'LBRACE' (if_stmt | while_loop | for_loop | expr)* 'RBRACE'"""
        comp_info = SubgraphInfo(self._cfg)
        self.match(TokenKind.LBRACE)
        prev_info = None
        while not self.check(TokenKind.RBRACE):
            token_pairs = [
                (TokenKind.IF, self.if_stmt),
                (TokenKind.WHILE, self.while_loop),
                (TokenKind.EXPR, self.expr)
            ]
            curr_info = None
            for token_kind, token_method in token_pairs:
                if self.check(token_kind):
                    curr_info = token_method()
                    break
            if curr_info is None:
                raise Exception(f"Failed to match token with any known kinds in `token_pairs`.")
            if prev_info is None:
                comp_info.entry = curr_info.entry
            else:
                prev_info.connect_next(curr_info)
            prev_info = curr_info
        if prev_info is None:
            no_op_info = self.no_op()
            comp_info.entry = no_op_info.entry
            comp_info.out_edges = no_op_info.out_edges
        else:
            comp_info.out_edges = prev_info.out_edges
        self.advance()
        return comp_info
    
    def if_stmt(self) -> SubgraphInfo:
        pass
    
    def expr(self) -> SubgraphInfo:
        return SubgraphInfo(self._cfg)
    
    def no_op(self) -> SubgraphInfo:
        no_op_info = SubgraphInfo(self._cfg)
        no_op_info.entry = self._cfg.new_node(NO_OP)
        no_op_info.add_oedge(Edge.NORMAL, no_op_info.entry)
        return no_op_info
    
    """
    These helper methods should be useful, and can be left as is.
    """ 
    def match(self, expect: TokenKind) -> None:
        if not self.check(expect):
            err_msg = (f"Failed matching token {self.curr_token()} with "
                       f"expectation {expect}.")
            raise Exception(err_msg)
        self.advance()
    
    def check(self, expect: TokenKind) -> bool:
        return self.curr_token().kind == expect
    
    def curr_token(self) -> Token:
        return self.tokens[self.curr_ind]
    
    def prev_token(self) -> Token:
        return self.tokens[self.curr_ind - 1]
    
    def advance(self):
        self.curr_ind += 1

