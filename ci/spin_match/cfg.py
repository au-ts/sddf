"""
This file provides a simple API for control flow graph generation.
"""

from enum import Enum
import pygraphviz as pgv


class Edge(Enum):
    NORMAL = ""
    TRUE = "T"
    FALSE = "F"


class CFG(pgv.AGraph):
    def __init__(self):
        self._num_nodes = 1
        self.add_node(0, label="START")
        super().__init__(directed=True)
    
    def new_node(self, node_str: str) -> int:
        """Given a string representation, creates a new node in the graph and
        returns its id."""
        node_id = self._num_nodes
        self._num_nodes += 1
        self.add_node(node_id, label=node_str)
        return node_id
    
    def connect_nodes(self, id1: int, id2: int, edge: Edge) -> None:
        """Given a source node id `id1`, and a destination node id `id2`, creates an
        edge between the nodes, with the label specified by `edge`."""
        self.add_edge(id1, id2, label=f" {edge.value}")

