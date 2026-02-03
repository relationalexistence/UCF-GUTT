"""
UCF/GUTT Network Metrics Engine - Polinode-Style Analytics
==========================================================

Copyright (C) 2023-2026 Michael Fillippini. All Rights Reserved.

25+ professional network metrics matching Polinode capabilities,
integrated with UCF/GUTT formally verified relational mathematics.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, Optional
from fractions import Fraction
from collections import defaultdict
import math

from ucf_core import MultiplexRelation, WeightedRelation
from org_analysis import OrganizationalNetwork, RelationshipChannel


@dataclass
class NodeMetrics:
    """Complete metrics for a single node."""
    node_id: str
    name: str
    role: str
    department: str
    
    # Degree metrics
    in_degree: int = 0
    out_degree: int = 0
    total_degree: int = 0
    weighted_in_degree: float = 0.0
    weighted_out_degree: float = 0.0
    weighted_total_degree: float = 0.0
    avg_neighbor_degree: float = 0.0
    
    # Centrality metrics
    betweenness: float = 0.0
    closeness: float = 0.0
    harmonic: float = 0.0
    eigenvector: float = 0.0
    pagerank: float = 0.0
    hub_score: float = 0.0
    authority_score: float = 0.0
    
    # Structural metrics
    clustering: float = 0.0
    constraint: float = 0.0
    effective_size: float = 0.0
    efficiency: float = 0.0
    core_number: int = 0
    
    # UCF/GUTT metrics
    relational_entropy: float = 0.0
    external_ratio: float = 0.0
    conflict_score: float = 0.0
    harmony_score: float = 0.0
    
    # Community
    community: int = 0


@dataclass
class NetworkStats:
    """Network-level summary statistics."""
    node_count: int = 0
    edge_count: int = 0
    density: float = 0.0
    avg_degree: float = 0.0
    avg_path_length: float = 0.0
    diameter: int = 0
    avg_clustering: float = 0.0
    conflict_count: int = 0
    harmony_count: int = 0
    seriality_satisfied: bool = True
    isolated_nodes: List[str] = field(default_factory=list)


class NetworkMetricsEngine:
    """Computes Polinode-style network metrics on UCF/GUTT OrganizationalNetwork."""
    
    def __init__(self, network: OrganizationalNetwork, channel: str = None):
        self.network = network
        self.channel = channel
        self.nodes = list(network.members.keys())
        self.n = len(self.nodes)
        self._build_adjacency()
    
    def _build_adjacency(self):
        self.adj_list = defaultdict(list)
        self.adj_matrix = {n1: {n2: 0.0 for n2 in self.nodes} for n1 in self.nodes}
        self.in_adj = defaultdict(list)
        self.out_adj = defaultdict(list)
        
        for source in self.nodes:
            for target in self.nodes:
                if source == target:
                    continue
                weight = float(self.network.relations.aggregate_weight(source, target)) if not self.channel else float(self.network.relations.get_weight(self.channel, source, target))
                if weight != 0:
                    self.out_adj[source].append((target, weight))
                    self.in_adj[target].append((source, weight))
                    if weight > 0:
                        self.adj_list[source].append((target, weight))
                        self.adj_list[target].append((source, weight))
                    self.adj_matrix[source][target] = weight
    
    def in_degree(self, node_id: str) -> int:
        return len(self.in_adj.get(node_id, []))
    
    def out_degree(self, node_id: str) -> int:
        return len(self.out_adj.get(node_id, []))
    
    def total_degree(self, node_id: str) -> int:
        return len(set(t for t, _ in self.out_adj.get(node_id, [])) | set(s for s, _ in self.in_adj.get(node_id, [])))
    
    def weighted_in_degree(self, node_id: str) -> float:
        return sum(abs(w) for _, w in self.in_adj.get(node_id, []))
    
    def weighted_out_degree(self, node_id: str) -> float:
        return sum(abs(w) for _, w in self.out_adj.get(node_id, []))
    
    def weighted_total_degree(self, node_id: str) -> float:
        return self.weighted_in_degree(node_id) + self.weighted_out_degree(node_id)
    
    def avg_neighbor_degree(self, node_id: str) -> float:
        neighbors = set(t for t, _ in self.out_adj.get(node_id, [])) | set(s for s, _ in self.in_adj.get(node_id, []))
        return sum(self.total_degree(n) for n in neighbors) / len(neighbors) if neighbors else 0.0
    
    def _bfs_distances(self, start_id: str) -> Dict[str, float]:
        dist = {n: float('inf') for n in self.nodes}
        dist[start_id] = 0
        queue = [start_id]
        while queue:
            current = queue.pop(0)
            for neighbor, w in self.out_adj.get(current, []) + self.in_adj.get(current, []):
                if w > 0 and dist[neighbor] == float('inf'):
                    dist[neighbor] = dist[current] + 1
                    queue.append(neighbor)
        return dist
    
    def betweenness_centrality(self) -> Dict[str, float]:
        betweenness = {n: 0.0 for n in self.nodes}
        for source in self.nodes:
            stack, pred, sigma, dist = [], {n: [] for n in self.nodes}, {n: 0.0 for n in self.nodes}, {n: -1 for n in self.nodes}
            sigma[source], dist[source] = 1.0, 0
            queue = [source]
            while queue:
                v = queue.pop(0)
                stack.append(v)
                neighbors = set(t for t, w in self.out_adj.get(v, []) if w > 0) | set(s for s, w in self.in_adj.get(v, []) if w > 0)
                for w in neighbors:
                    if dist[w] < 0:
                        queue.append(w)
                        dist[w] = dist[v] + 1
                    if dist[w] == dist[v] + 1:
                        sigma[w] += sigma[v]
                        pred[w].append(v)
            delta = {n: 0.0 for n in self.nodes}
            while stack:
                w = stack.pop()
                for v in pred[w]:
                    delta[v] += (sigma[v] / sigma[w]) * (1 + delta[w])
                if w != source:
                    betweenness[w] += delta[w]
        norm = (self.n - 1) * (self.n - 2) if self.n > 2 else 1
        return {k: v / norm for k, v in betweenness.items()}
    
    def closeness_centrality(self) -> Dict[str, float]:
        return {node: (len([d for d in self._bfs_distances(node).values() if 0 < d < float('inf')]) / sum(d for d in self._bfs_distances(node).values() if 0 < d < float('inf')) if sum(d for d in self._bfs_distances(node).values() if 0 < d < float('inf')) else 0.0) for node in self.nodes}
    
    def harmonic_centrality(self) -> Dict[str, float]:
        return {node: sum(1/d for t, d in self._bfs_distances(node).items() if t != node and 0 < d < float('inf')) / (self.n - 1) if self.n > 1 else 0 for node in self.nodes}
    
    def eigenvector_centrality(self, iterations: int = 50) -> Dict[str, float]:
        scores = {n: 1.0 / self.n for n in self.nodes}
        for _ in range(iterations):
            new_scores = {n: sum(scores.get(nb, 0) * w for nb, w in self.adj_list.get(n, []) if w > 0) for n in self.nodes}
            max_score = max(new_scores.values()) or 0.001
            scores = {k: v / max_score for k, v in new_scores.items()}
        return scores
    
    def pagerank(self, damping: float = 0.85, iterations: int = 50) -> Dict[str, float]:
        scores = {n: 1.0 / self.n for n in self.nodes}
        for _ in range(iterations):
            new_scores = {n: (1 - damping) / self.n for n in self.nodes}
            for node in self.nodes:
                neighbors = self.adj_list.get(node, [])
                if neighbors:
                    share = damping * scores[node] / len(neighbors)
                    for neighbor, _ in neighbors:
                        new_scores[neighbor] += share
            scores = new_scores
        return scores
    
    def hits(self, iterations: int = 50) -> Tuple[Dict[str, float], Dict[str, float]]:
        hubs, authorities = {n: 1.0 for n in self.nodes}, {n: 1.0 for n in self.nodes}
        for _ in range(iterations):
            new_auth = {node: sum(hubs.get(src, 0) for src, _ in self.in_adj.get(node, [])) for node in self.nodes}
            new_hubs = {node: sum(new_auth.get(tgt, 0) for tgt, _ in self.out_adj.get(node, [])) for node in self.nodes}
            auth_norm, hub_norm = math.sqrt(sum(v*v for v in new_auth.values())) or 1, math.sqrt(sum(v*v for v in new_hubs.values())) or 1
            authorities, hubs = {k: v / auth_norm for k, v in new_auth.items()}, {k: v / hub_norm for k, v in new_hubs.items()}
        return hubs, authorities
    
    def clustering_coefficient(self, node_id: str) -> float:
        neighbors = self.adj_list.get(node_id, [])
        k = len(neighbors)
        if k < 2:
            return 0.0
        neighbor_ids = [n for n, _ in neighbors]
        triangles = sum(1 for i, n1 in enumerate(neighbor_ids) for n2 in neighbor_ids[i+1:] if self.adj_matrix.get(n1, {}).get(n2, 0) > 0)
        return (2 * triangles) / (k * (k - 1))
    
    def constraint(self, node_id: str) -> float:
        neighbors = self.adj_list.get(node_id, [])
        if not neighbors:
            return 1.0
        n_neighbors = len(neighbors)
        total = 0.0
        for j, _ in neighbors:
            pij = 1.0 / n_neighbors
            indirect = sum((1.0 / n_neighbors) * ((1.0 / len(self.adj_list.get(q, [(None, 0)]))) if self.adj_matrix.get(q, {}).get(j, 0) > 0 else 0) for q, _ in neighbors if q != j)
            total += (pij + indirect) ** 2
        return total
    
    def effective_size(self, node_id: str) -> float:
        neighbors = self.adj_list.get(node_id, [])
        if not neighbors:
            return 0.0
        neighbor_ids = [n for n, _ in neighbors]
        redundancy = sum(1 for n1 in neighbor_ids for n2 in neighbor_ids if n1 != n2 and self.adj_matrix.get(n1, {}).get(n2, 0) > 0)
        return len(neighbors) - (redundancy / max(len(neighbors), 1))
    
    def efficiency(self, node_id: str) -> float:
        degree = self.total_degree(node_id)
        return self.effective_size(node_id) / degree if degree > 0 else 0.0
    
    def core_number(self) -> Dict[str, int]:
        cores, remaining = {}, set(self.nodes)
        k = 0
        while remaining:
            changed = True
            while changed:
                changed = False
                to_remove = [n for n in remaining if len([nb for nb, _ in self.adj_list.get(n, []) if nb in remaining]) <= k]
                for node in to_remove:
                    cores[node] = k
                    remaining.discard(node)
                    changed = True
            k += 1
        return cores
    
    def relational_entropy(self, node_id: str) -> float:
        neighbors = list(self.out_adj.get(node_id, [])) + list(self.in_adj.get(node_id, []))
        if not neighbors:
            return 0.0
        total_weight = sum(abs(w) for _, w in neighbors)
        if total_weight == 0:
            return 0.0
        return -sum((abs(w) / total_weight) * math.log2(abs(w) / total_weight) for _, w in neighbors if abs(w) > 0)
    
    def external_ratio(self, node_id: str) -> float:
        member = self.network.members.get(node_id)
        if not member:
            return 0.0
        my_dept = member.department
        neighbors = set(t for t, _ in self.out_adj.get(node_id, [])) | set(s for s, _ in self.in_adj.get(node_id, []))
        if not neighbors:
            return 0.0
        return sum(1 for n in neighbors if self.network.members.get(n) and self.network.members[n].department != my_dept) / len(neighbors)
    
    def conflict_score(self, node_id: str) -> float:
        relations, conflicts = 0, 0
        for other_id in self.nodes:
            if other_id == node_id:
                continue
            if any(self.network.relations.get_weight(ch.value, node_id, other_id) != 0 for ch in RelationshipChannel):
                relations += 1
                if self.network.relations.has_conflict(node_id, other_id):
                    conflicts += 1
            if any(self.network.relations.get_weight(ch.value, other_id, node_id) != 0 for ch in RelationshipChannel):
                relations += 1
                if self.network.relations.has_conflict(other_id, node_id):
                    conflicts += 1
        return conflicts / relations if relations > 0 else 0.0
    
    def harmony_score(self, node_id: str) -> float:
        relations, harmonies = 0, 0
        for other_id in self.nodes:
            if other_id == node_id:
                continue
            if any(self.network.relations.get_weight(ch.value, node_id, other_id) != 0 for ch in RelationshipChannel):
                relations += 1
                if self.network.relations.has_harmony(node_id, other_id):
                    harmonies += 1
            if any(self.network.relations.get_weight(ch.value, other_id, node_id) != 0 for ch in RelationshipChannel):
                relations += 1
                if self.network.relations.has_harmony(other_id, node_id):
                    harmonies += 1
        return harmonies / relations if relations > 0 else 0.0
    
    def density(self) -> float:
        if self.n <= 1:
            return 0.0
        return sum(len(adj) for adj in self.out_adj.values()) / (self.n * (self.n - 1))
    
    def average_degree(self) -> float:
        return sum(self.total_degree(n) for n in self.nodes) / self.n if self.n > 0 else 0.0
    
    def average_path_length(self) -> float:
        total, count = 0, 0
        for node in self.nodes:
            for t, d in self._bfs_distances(node).items():
                if t != node and d < float('inf'):
                    total += d
                    count += 1
        return total / count if count > 0 else 0.0
    
    def diameter(self) -> int:
        return max(max((int(d) for d in self._bfs_distances(n).values() if d < float('inf')), default=0) for n in self.nodes)
    
    def average_clustering(self) -> float:
        return sum(self.clustering_coefficient(n) for n in self.nodes) / self.n if self.n > 0 else 0.0
    
    def compute_all_node_metrics(self) -> List[NodeMetrics]:
        betweenness, closeness, harmonic = self.betweenness_centrality(), self.closeness_centrality(), self.harmonic_centrality()
        eigenvector, pr = self.eigenvector_centrality(), self.pagerank()
        hubs, authorities = self.hits()
        cores = self.core_number()
        results = []
        for node_id in self.nodes:
            member = self.network.members.get(node_id)
            if not member:
                continue
            results.append(NodeMetrics(
                node_id=node_id, name=member.name, role=member.role, department=member.department,
                in_degree=self.in_degree(node_id), out_degree=self.out_degree(node_id), total_degree=self.total_degree(node_id),
                weighted_in_degree=self.weighted_in_degree(node_id), weighted_out_degree=self.weighted_out_degree(node_id),
                weighted_total_degree=self.weighted_total_degree(node_id), avg_neighbor_degree=self.avg_neighbor_degree(node_id),
                betweenness=betweenness.get(node_id, 0), closeness=closeness.get(node_id, 0), harmonic=harmonic.get(node_id, 0),
                eigenvector=eigenvector.get(node_id, 0), pagerank=pr.get(node_id, 0), hub_score=hubs.get(node_id, 0), authority_score=authorities.get(node_id, 0),
                clustering=self.clustering_coefficient(node_id), constraint=self.constraint(node_id), effective_size=self.effective_size(node_id),
                efficiency=self.efficiency(node_id), core_number=cores.get(node_id, 0), relational_entropy=self.relational_entropy(node_id),
                external_ratio=self.external_ratio(node_id), conflict_score=self.conflict_score(node_id), harmony_score=self.harmony_score(node_id),
            ))
        return results
    
    def compute_network_metrics(self) -> NetworkStats:
        conflict_pairs, harmony_pairs = self.network.relations.conflict_pairs(), self.network.relations.harmony_pairs()
        from ucf_core import check_seriality
        wr = WeightedRelation(self.nodes)
        for source in self.nodes:
            for target in self.nodes:
                if source != target:
                    agg = self.network.relations.aggregate_weight(source, target)
                    if agg != 0:
                        wr.set_weight(source, target, agg)
        is_serial, isolated = check_seriality(wr)
        return NetworkStats(
            node_count=self.n, edge_count=sum(len(adj) for adj in self.out_adj.values()), density=self.density(),
            avg_degree=self.average_degree(), avg_path_length=self.average_path_length(), diameter=self.diameter(),
            avg_clustering=self.average_clustering(), conflict_count=len(conflict_pairs), harmony_count=len(harmony_pairs),
            seriality_satisfied=is_serial, isolated_nodes=isolated,
        )


def analyze_network(network, channel=None):
    engine = NetworkMetricsEngine(network, channel)
    return engine.compute_all_node_metrics(), engine.compute_network_metrics()
