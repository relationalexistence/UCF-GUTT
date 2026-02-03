"""
UCF/GUTT™ Organizational Network Analyzer — ENHANCED DEMO VERSION
===================================================================

PROPRIETARY AND CONFIDENTIAL
Copyright (C) 2023-2026 Michael Fillippini. All Rights Reserved.

ENHANCEMENTS IN THIS VERSION:
  • 25+ Polinode-style network metrics (betweenness, PageRank, etc.)
  • Network graph visualization (NetworkX + Altair)
  • Multiple sample datasets
  • Fully interactive playgrounds
  • Heatmap adjacency matrix view
  • Detailed metrics table with sorting
  • Unit test coverage

Run with: streamlit run app.py
"""

import streamlit as st
import pandas as pd
import json
from fractions import Fraction
from typing import Dict, List, Tuple, Optional
import math

from ucf_core import RelationSign
from org_analysis import (
    OrganizationalNetwork,
    TeamMember,
    RelationshipChannel,
    create_sample_network,
    TeamHealthReport,
    ConflictReport,
    IsolationReport
)

# Import the new metrics engine
try:
    from network_metrics import NetworkMetricsEngine, NodeMetrics, NetworkStats, analyze_network
    HAS_METRICS_ENGINE = True
except ImportError:
    HAS_METRICS_ENGINE = False

# Try to import visualization libraries
try:
    import networkx as nx
    import altair as alt
    HAS_VISUALIZATION = True
except ImportError:
    HAS_VISUALIZATION = False

# Try to import sample datasets
try:
    from sample_datasets import get_sample_datasets
    HAS_SAMPLE_DATASETS = True
except ImportError:
    HAS_SAMPLE_DATASETS = False
    def get_sample_datasets():
        return {"Engineering Team (Default)": create_sample_network}

# Page configuration
st.set_page_config(
    page_title="UCF/GUTT ONA Analyzer",
    page_icon="🔬",
    layout="wide"
)

# Custom CSS
st.markdown("""
<style>
    .metric-card { background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); padding: 20px; border-radius: 10px; color: white; margin: 10px 0; }
    .conflict-high { background-color: #ffcdd2; padding: 10px; border-radius: 5px; margin: 5px 0; }
    .conflict-medium { background-color: #fff9c4; padding: 10px; border-radius: 5px; margin: 5px 0; }
    .conflict-low { background-color: #e8f5e9; padding: 10px; border-radius: 5px; margin: 5px 0; }
    .isolation-warning { background-color: #ffecb3; padding: 10px; border-radius: 5px; margin: 5px 0; }
    .formal-note { background-color: #e3f2fd; border-left: 4px solid #1976d2; padding: 10px; margin: 10px 0; font-size: 0.9em; }
    .verified-badge { background-color: #4caf50; color: white; padding: 3px 8px; border-radius: 3px; font-size: 0.8em; }
    .polinode-badge { background-color: #2196f3; color: white; padding: 3px 8px; border-radius: 3px; font-size: 0.8em; }
    .error-message { background-color: #ffebee; border-left: 4px solid #f44336; padding: 10px; margin: 10px 0; }
    .success-message { background-color: #e8f5e9; border-left: 4px solid #4caf50; padding: 10px; margin: 10px 0; }
    .info-message { background-color: #e3f2fd; border-left: 4px solid #2196f3; padding: 10px; margin: 10px 0; }
</style>
""", unsafe_allow_html=True)


def show_error(message: str):
    st.markdown(f'<div class="error-message">❌ {message}</div>', unsafe_allow_html=True)

def show_success(message: str):
    st.markdown(f'<div class="success-message">✅ {message}</div>', unsafe_allow_html=True)

def show_info(message: str):
    st.markdown(f'<div class="info-message">ℹ️ {message}</div>', unsafe_allow_html=True)


def create_network_graph(network: OrganizationalNetwork, channel: str = None):
    """Create network visualization using NetworkX and Altair."""
    if not HAS_VISUALIZATION or not network.members:
        return None
    
    try:
        G = nx.DiGraph()
        for m_id, member in network.members.items():
            G.add_node(m_id, name=member.name, role=member.role, department=member.department)
        
        for source_id in network.members:
            for target_id in network.members:
                if source_id == target_id:
                    continue
                if channel:
                    weight = float(network.relations.get_weight(channel, source_id, target_id))
                else:
                    weight = float(network.relations.aggregate_weight(source_id, target_id))
                if weight != 0:
                    G.add_edge(source_id, target_id, weight=weight)
        
        if len(G.edges()) == 0:
            return None
        
        pos = nx.spring_layout(G, k=2, iterations=50, seed=42)
        
        nodes_data = []
        for node, (x, y) in pos.items():
            member = network.members.get(node)
            if member:
                # Check for problems: conflict (mixed signals) OR hostile (all negative)
                has_problem = False
                problem_type = None
                
                for other in network.members:
                    if other == node:
                        continue
                    # Check both directions
                    if network.relations.has_conflict(node, other) or network.relations.has_conflict(other, node):
                        has_problem = True
                        problem_type = "conflict"
                        break
                    # Check for hostile (all negative, no positive) in either direction
                    pos_out = sum(1 for ch in RelationshipChannel if float(network.relations.get_weight(ch.value, node, other)) > 0)
                    neg_out = sum(1 for ch in RelationshipChannel if float(network.relations.get_weight(ch.value, node, other)) < 0)
                    pos_in = sum(1 for ch in RelationshipChannel if float(network.relations.get_weight(ch.value, other, node)) > 0)
                    neg_in = sum(1 for ch in RelationshipChannel if float(network.relations.get_weight(ch.value, other, node)) < 0)
                    
                    if (neg_out > 0 and pos_out == 0) or (neg_in > 0 and pos_in == 0):
                        has_problem = True
                        problem_type = "hostile"
                        break
                
                nodes_data.append({
                    'id': node, 'name': member.name, 'role': member.role,
                    'x': x, 'y': y, 'has_conflict': has_problem,
                    'color': '#ff5252' if has_problem else '#4caf50'
                })
        
        nodes_df = pd.DataFrame(nodes_data)
        
        edges_data = []
        for source, target, data in G.edges(data=True):
            weight = data.get('weight', 0)
            edges_data.append({
                'source': source, 'target': target,
                'x': pos[source][0], 'y': pos[source][1],
                'x2': pos[target][0], 'y2': pos[target][1],
                'weight': weight, 'color': '#4caf50' if weight > 0 else '#f44336',
                'stroke_width': min(abs(weight) * 3 + 1, 5)
            })
        
        edges_df = pd.DataFrame(edges_data)
        
        edges_chart = alt.Chart(edges_df).mark_line(strokeWidth=2, opacity=0.6).encode(
            x=alt.X('x:Q', axis=None), y=alt.Y('y:Q', axis=None),
            x2='x2:Q', y2='y2:Q',
            color=alt.Color('color:N', scale=None),
            strokeWidth=alt.StrokeWidth('stroke_width:Q', scale=None),
            tooltip=['source:N', 'target:N', 'weight:Q']
        )
        
        # Create initials for display inside circle
        def get_initials(name):
            parts = str(name).split()
            if len(parts) >= 2:
                return (parts[0][0] + parts[1][0]).upper()
            return str(name)[:2].upper()
        
        # Build unique display names
        all_names = list(nodes_df['name'])
        display_names = {}
        
        for name in all_names:
            parts = str(name).split()
            first = parts[0] if parts else str(name)
            last = parts[-1] if len(parts) > 1 else ""
            
            # Start with just first name
            display = first
            
            # Check if unique
            others_with_same = [n for n in all_names if n != name and str(n).split()[0] == first]
            
            if others_with_same and last:
                # Try "First L."
                display = f"{first} {last[0]}."
                
                # Check if still duplicate
                for other in others_with_same:
                    other_parts = str(other).split()
                    other_last = other_parts[-1] if len(other_parts) > 1 else ""
                    if other_last and other_last[0] == last[0]:
                        # Same first name and last initial - use more of last name
                        # Try first 2 chars, then 3, etc.
                        for length in range(2, len(last) + 1):
                            display = f"{first} {last[:length]}."
                            conflict = False
                            for o in others_with_same:
                                o_parts = str(o).split()
                                o_last = o_parts[-1] if len(o_parts) > 1 else ""
                                if o_last[:length] == last[:length]:
                                    conflict = True
                                    break
                            if not conflict:
                                break
                        else:
                            # Last resort: full name
                            display = name
                        break
            
            display_names[name] = display
        
        nodes_df['initials'] = nodes_df['name'].apply(get_initials)
        nodes_df['short_name'] = nodes_df['name'].apply(lambda x: display_names.get(x, x))
        
        # Larger nodes
        nodes_chart = alt.Chart(nodes_df).mark_circle(size=1800, stroke='white', strokeWidth=2).encode(
            x=alt.X('x:Q', axis=None), y=alt.Y('y:Q', axis=None),
            color=alt.Color('color:N', scale=None),
            tooltip=['name:N', 'role:N', 'has_conflict:N']
        )
        
        # Initials inside circle
        initials_chart = alt.Chart(nodes_df).mark_text(fontSize=12, fontWeight='bold').encode(
            x='x:Q', y='y:Q', text='initials:N',
            color=alt.value('white')
        )
        
        # First name below circle (with last name disambiguation if needed)
        labels_chart = alt.Chart(nodes_df).mark_text(fontSize=10, dy=32).encode(
            x='x:Q', y='y:Q', text='short_name:N',
            color=alt.value('#374151')
        )
        
        return (edges_chart + nodes_chart + initials_chart + labels_chart).properties(width=600, height=400).configure_view(strokeWidth=0)
    
    except Exception as e:
        st.warning(f"Could not create visualization: {e}")
        return None


def sync_playground_to_network(network: OrganizationalNetwork) -> int:
    """Sync playground slider values to the network.
    
    Reads directly from Streamlit slider session_state keys (pg_source_target_channel)
    and updates the network. This runs BEFORE any tab renders, ensuring all views
    see the updated values.
    
    Returns count of synced values.
    """
    if not network.members:
        return 0
    
    synced_count = 0
    members = list(network.members.keys())
    
    # Read ALL slider keys and apply to network
    for source in members:
        for target in members:
            if source == target:
                continue
            for ch in RelationshipChannel:
                slider_key = f"pg_{source}_{target}_{ch.value}"
                if slider_key in st.session_state:
                    weight = float(st.session_state[slider_key])
                    # Get current network value
                    current = float(network.relations.get_weight(ch.value, source, target))
                    # Only count if different (to show real syncs)
                    if abs(weight - current) > 0.001:
                        synced_count += 1
                    network.set_relationship(source, target, ch, weight)
    
    return synced_count


def init_playground_from_network(network: OrganizationalNetwork):
    """Initialize playground weights from current network state."""
    if 'playground_weights' in st.session_state:
        return
    st.session_state.playground_weights = {}
    for source_id in network.members:
        for target_id in network.members:
            if source_id == target_id:
                continue
            weights = {}
            has_any = False
            for ch in RelationshipChannel:
                w = network.relations.get_weight(ch.value, source_id, target_id)
                weights[ch.value] = float(w)
                if w != 0:
                    has_any = True
            if has_any:
                st.session_state.playground_weights[(source_id, target_id)] = weights


def render_header():
    # DEMO BANNER - Prominent warning
    st.markdown("""
    <div style="background: linear-gradient(135deg, #dc2626 0%, #ea580c 100%); 
                color: white; padding: 15px 20px; border-radius: 10px; margin-bottom: 20px;
                border: 3px solid #fbbf24; text-align: center;">
        <div style="font-size: 22px; font-weight: bold; margin-bottom: 5px;">
            ⚠️ DEMONSTRATION VERSION
        </div>
        <div style="font-size: 14px; opacity: 0.95;">
            Simplified algorithms for concept illustration | Production system uses proprietary UCF/GUTT methods
        </div>
        <div style="margin-top: 10px;">
            <a href="https://relationalexistence.com" style="color: #fef08a; text-decoration: none; font-weight: bold; font-size: 15px;">
            🔒 Contact for Production License →</a>
        </div>
    </div>
    """, unsafe_allow_html=True)
    
    st.title("🔬 UCF/GUTT Organizational Network Analyzer")
    st.markdown("""
    <div class="formal-note">
    <strong>Demo Version</strong> — Illustrates relational analysis concepts.
    <span class="polinode-badge">DEMO</span>
    <br><small>⚠️ Scores use simplified formulas. Production has calibrated analysis.</small>
    <br><a href="https://relationalexistence.com">relationalexistence.com</a> | 
    <a href="mailto:Michael_Fill@ProtonMail.com">Michael_Fill@ProtonMail.com</a>
    </div>
    """, unsafe_allow_html=True)


def render_sidebar():
    """Render sidebar for data input."""
    st.sidebar.header("📊 Data Management")
    
    st.sidebar.subheader("Load Sample Dataset")
    datasets = get_sample_datasets()
    selected_dataset = st.sidebar.selectbox("Choose dataset", list(datasets.keys()), key="dataset_selector")
    
    if st.sidebar.button("📂 Load Dataset", key="load_dataset_btn"):
        try:
            if 'playground_weights' in st.session_state:
                del st.session_state.playground_weights
            st.session_state.network = datasets[selected_dataset]()
            st.session_state.data_loaded = True
            show_success(f"Loaded: {selected_dataset}")
            st.rerun()
        except Exception as e:
            show_error(f"Failed to load dataset: {e}")
    
    st.sidebar.markdown("---")
    
    st.sidebar.subheader("➕ Add Team Member")
    with st.sidebar.form("add_member"):
        member_id = st.text_input("ID (unique)")
        member_name = st.text_input("Name")
        member_role = st.text_input("Role")
        member_dept = st.text_input("Department")
        
        if st.form_submit_button("Add Member"):
            if not member_id or not member_name:
                show_error("ID and Name are required")
            elif 'network' in st.session_state and member_id in st.session_state.network.members:
                show_error(f"Member ID '{member_id}' already exists")
            else:
                if 'network' not in st.session_state:
                    st.session_state.network = OrganizationalNetwork("My Team")
                st.session_state.network.add_member(TeamMember(member_id, member_name, member_role, member_dept))
                st.session_state.data_loaded = True
                show_success(f"Added {member_name}")
                st.rerun()
    
    st.sidebar.markdown("---")
    
    if 'network' in st.session_state and len(st.session_state.network.members) >= 2:
        st.sidebar.subheader("🔗 Add Relationship")
        with st.sidebar.form("add_relationship"):
            members = list(st.session_state.network.members.keys())
            source = st.selectbox("From", members, format_func=lambda x: st.session_state.network.members[x].name, key="rel_source")
            target_options = [m for m in members if m != source]
            target = st.selectbox("To", target_options, format_func=lambda x: st.session_state.network.members[x].name, key="rel_target")
            channel = st.selectbox("Channel", [c.value for c in RelationshipChannel])
            weight = st.slider("Weight", -1.0, 1.0, 0.5, 0.1)
            
            if st.form_submit_button("Add Relationship"):
                try:
                    st.session_state.network.set_relationship(source, target, RelationshipChannel(channel), weight)
                    if 'playground_weights' in st.session_state:
                        pair_key = (source, target)
                        if pair_key not in st.session_state.playground_weights:
                            st.session_state.playground_weights[pair_key] = {ch.value: 0.0 for ch in RelationshipChannel}
                        st.session_state.playground_weights[pair_key][channel] = weight
                    show_success(f"Added {channel} relationship")
                    st.rerun()
                except Exception as e:
                    show_error(f"Failed: {e}")
    
    st.sidebar.markdown("---")
    st.sidebar.subheader("💾 Export/Import")
    
    if 'network' in st.session_state:
        try:
            export_data = json.dumps(st.session_state.network.to_dict(), indent=2)
            st.sidebar.download_button("📥 Export JSON", export_data, file_name="team_network.json", mime="application/json")
        except Exception as e:
            show_error(f"Export failed: {e}")
    
    uploaded = st.sidebar.file_uploader("📤 Import JSON", type="json")
    if uploaded:
        try:
            data = json.load(uploaded)
            st.session_state.network = OrganizationalNetwork.from_dict(data)
            st.session_state.data_loaded = True
            if 'playground_weights' in st.session_state:
                del st.session_state.playground_weights
            show_success("Imported successfully")
            st.rerun()
        except Exception as e:
            show_error(f"Import failed: {e}")
    
    # Production comparison - always visible in sidebar
    st.sidebar.markdown("---")
    st.sidebar.markdown("""
    <div style="background: linear-gradient(135deg, #1e3a5f 0%, #2d4a6f 100%); 
                padding: 15px; border-radius: 10px; border: 2px solid #fbbf24;">
        <div style="color: #fbbf24; font-weight: bold; font-size: 14px; margin-bottom: 10px;">
            🔒 PRODUCTION ADDS
        </div>
        <table style="width: 100%; font-size: 11px; color: white;">
            <tr>
                <td style="padding: 3px 0;">📊 Health Scoring</td>
                <td style="color: #fca5a5;">Demo: Basic</td>
            </tr>
            <tr>
                <td></td>
                <td style="color: #86efac;">Prod: Calibrated</td>
            </tr>
            <tr>
                <td style="padding: 3px 0;">⚡ Conflict Detection</td>
                <td style="color: #fca5a5;">Demo: Simple</td>
            </tr>
            <tr>
                <td></td>
                <td style="color: #86efac;">Prod: Tensor Analysis</td>
            </tr>
            <tr>
                <td style="padding: 3px 0;">🔬 Verification</td>
                <td style="color: #fca5a5;">Demo: None</td>
            </tr>
            <tr>
                <td></td>
                <td style="color: #86efac;">Prod: 100K+ Coq</td>
            </tr>
            <tr>
                <td style="padding: 3px 0;">📈 Prediction</td>
                <td style="color: #fca5a5;">Demo: None</td>
            </tr>
            <tr>
                <td></td>
                <td style="color: #86efac;">Prod: Risk Modeling</td>
            </tr>
        </table>
        <div style="margin-top: 12px; text-align: center;">
            <a href="mailto:Michael_Fill@ProtonMail.com" 
               style="color: #fbbf24; text-decoration: none; font-weight: bold; font-size: 12px;">
            ✉️ License Inquiry →</a>
        </div>
    </div>
    """, unsafe_allow_html=True)


def render_metrics(report: TeamHealthReport):
    """Render key metrics with visualization."""
    st.header("📈 Key Metrics")
    
    # Show that this reflects current network state
    if 'network' in st.session_state:
        # Count active playground sliders
        slider_count = sum(1 for key in st.session_state.keys() if key.startswith('pg_'))
        if slider_count > 0:
            st.caption(f"📡 Live data from {slider_count} playground sliders")
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        score = report.overall_health_score()
        color = "🟢" if score >= 70 else "🟡" if score >= 50 else "🔴"
        st.metric(f"{color} Overall Health", f"{score:.0f}/100")
    
    with col2:
        st.metric("📊 Connectivity", f"{report.connectivity_density:.0%}")
    
    with col3:
        sentiment_icon = "😊" if report.sentiment_balance > 0.2 else "😐" if report.sentiment_balance > -0.2 else "😟"
        st.metric(f"{sentiment_icon} Sentiment", f"{report.sentiment_balance:+.0%}")
    
    with col4:
        st.metric("🎯 Alignment", f"{report.channel_alignment:.0%}")
    
    if report.seriality_satisfied:
        st.success("✅ **Seriality Satisfied**: Every team member has connections")
    else:
        st.error("⚠️ **Seriality Violation**: Some team members lack connections")
    
    if HAS_VISUALIZATION and 'network' in st.session_state:
        st.markdown("---")
        st.subheader("🕸️ Network Visualization")
        
        # Show live indicator if playground has been used
        slider_keys = [k for k in st.session_state.keys() if k.startswith('pg_')]
        if slider_keys:
            st.caption("🔄 Live view - reflects playground changes")
        
        col1, col2 = st.columns([3, 1])
        with col2:
            viz_channel = st.selectbox("Channel", ["Aggregate"] + [c.value for c in RelationshipChannel], key="viz_channel")
            st.caption("🔴 = conflict/hostile in either direction")
        
        with col1:
            channel_val = None if viz_channel == "Aggregate" else viz_channel
            # Force fresh graph - the network object has already been synced with playground
            chart = create_network_graph(st.session_state.network, channel_val)
            if chart:
                st.altair_chart(chart, use_container_width=True)
            else:
                show_info("Add relationships to see the network graph")
    
    # Recommendations
    st.markdown("---")
    st.header("💡 Recommendations")
    for i, rec in enumerate(report.recommendations, 1):
        st.markdown(f"**{i}.** {rec}")


def render_polinode_metrics(network: OrganizationalNetwork):
    """Render the 25+ Polinode-style network metrics."""
    st.header("📊 Network Metrics (25+ Polinode-Style)")
    
    st.markdown("""
    <div class="formal-note">
    <span class="polinode-badge">POLINODE-STYLE</span>
    Professional ONA metrics including centrality, structural holes, and UCF/GUTT unique measures.
    <br><em>Reflects current network state including any Playground changes.</em>
    </div>
    """, unsafe_allow_html=True)
    
    if not HAS_METRICS_ENGINE:
        st.error("Metrics engine not available. Ensure network_metrics.py is present.")
        return
    
    if not network.members:
        show_info("Add team members to see network metrics")
        return
    
    try:
        node_metrics, network_stats = analyze_network(network)
        
        # Network-level stats
        st.subheader("🌐 Network-Level Statistics")
        cols = st.columns(5)
        with cols[0]:
            st.metric("Nodes", network_stats.node_count)
        with cols[1]:
            st.metric("Edges", network_stats.edge_count)
        with cols[2]:
            st.metric("Density", f"{network_stats.density:.1%}")
        with cols[3]:
            st.metric("Avg Path", f"{network_stats.avg_path_length:.2f}")
        with cols[4]:
            st.metric("Diameter", network_stats.diameter)
        
        cols2 = st.columns(4)
        with cols2[0]:
            st.metric("R_conflict", network_stats.conflict_count, delta="⚠️" if network_stats.conflict_count > 0 else None)
        with cols2[1]:
            st.metric("R_harmony", network_stats.harmony_count)
        with cols2[2]:
            st.metric("Avg Clustering", f"{network_stats.avg_clustering:.1%}")
        with cols2[3]:
            st.metric("Seriality", "✓" if network_stats.seriality_satisfied else "✗")
        
        st.markdown("---")
        
        # Node-level metrics table
        st.subheader("👤 Node-Level Metrics")
        
        col1, col2 = st.columns([2, 1])
        with col1:
            sort_by = st.selectbox("Sort by", 
                ["PageRank", "Betweenness", "Closeness", "Eigenvector", "Total Degree", 
                 "Clustering", "Constraint", "Entropy", "Authority", "Hub Score"], key="metrics_sort")
        with col2:
            sort_order = st.radio("Order", ["Descending", "Ascending"], horizontal=True)
        
        data = []
        for m in node_metrics:
            data.append({
                "Name": m.name, "Role": m.role, "Dept": m.department,
                "In°": m.in_degree, "Out°": m.out_degree, "Total°": m.total_degree,
                "Betweenness": f"{m.betweenness:.1%}",
                "Closeness": f"{m.closeness:.3f}",
                "PageRank": f"{m.pagerank:.1%}",
                "Eigenvector": f"{m.eigenvector:.3f}",
                "Hub": f"{m.hub_score:.3f}",
                "Authority": f"{m.authority_score:.3f}",
                "Clustering": f"{m.clustering:.0%}",
                "Constraint": f"{m.constraint:.2f}",
                "Eff.Size": f"{m.effective_size:.1f}",
                "Entropy": f"{m.relational_entropy:.2f}",
                "Ext%": f"{m.external_ratio:.0%}",
                "Core#": m.core_number,
                "Conflict": "⚠️" if m.conflict_score > 0 else "✓",
                "_pr": m.pagerank, "_bt": m.betweenness, "_cl": m.closeness,
                "_ev": m.eigenvector, "_dg": m.total_degree, "_cs": m.clustering,
                "_cn": m.constraint, "_en": m.relational_entropy,
                "_au": m.authority_score, "_hu": m.hub_score,
            })
        
        df = pd.DataFrame(data)
        
        sort_map = {"PageRank": "_pr", "Betweenness": "_bt", "Closeness": "_cl",
                   "Eigenvector": "_ev", "Total Degree": "_dg", "Clustering": "_cs",
                   "Constraint": "_cn", "Entropy": "_en", "Authority": "_au", "Hub Score": "_hu"}
        sort_col = sort_map.get(sort_by, "_pr")
        df = df.sort_values(sort_col, ascending=(sort_order == "Ascending"))
        
        display_cols = [c for c in df.columns if not c.startswith("_")]
        st.dataframe(df[display_cols], use_container_width=True, hide_index=True)
        
        with st.expander("📖 Metric Definitions"):
            st.markdown("""
            **Centrality:** Betweenness (broker), Closeness (reach), PageRank (influence), Eigenvector (connected to influencers)
            
            **HITS:** Hub (links to authorities), Authority (linked by hubs)
            
            **Structural Holes:** Constraint (redundancy), Effective Size (non-redundant ties)
            
            **UCF/GUTT:** Entropy (connection diversity), External% (cross-department links)
            """)
        
    except Exception as e:
        st.error(f"Error calculating metrics: {e}")
        import traceback
        st.code(traceback.format_exc())


def render_heatmap_matrix(network: OrganizationalNetwork):
    """Render adjacency matrix as a clean HTML heatmap table with hover details."""
    st.header("🔲 Adjacency Heatmap")
    
    if not network.members:
        show_info("Add team members to see the heatmap")
        return
    
    # Show live indicator if playground has been used
    slider_keys = [k for k in st.session_state.keys() if k.startswith('pg_')]
    if slider_keys:
        st.success("🔄 **Live view** - reflects playground changes")
    
    st.markdown("""
    <div class="formal-note">
    Visual representation of relationship strengths. 
    <span style="color: #22c55e;">■</span> Green = Positive | 
    <span style="color: #ef4444;">■</span> Red = Negative | 
    <span style="color: #6b7280;">■</span> Gray = Zero
    <br><em>💡 Hover over cells for channel details</em>
    </div>
    """, unsafe_allow_html=True)
    
    view_option = st.selectbox("View", ["Aggregate"] + [c.value.title() for c in RelationshipChannel], key="heatmap_view")
    
    members = list(network.members.keys())
    member_names = {m: network.members[m].name for m in members}
    
    # Build HTML table - clean and reliable
    html = '''
    <style>
        .heatmap-table { border-collapse: collapse; width: 100%; margin: 10px 0; }
        .heatmap-table th, .heatmap-table td { 
            padding: 10px 8px; 
            text-align: center; 
            font-size: 13px;
            border: 1px solid #334155;
            cursor: pointer;
            position: relative;
        }
        .heatmap-table th { 
            background: #1e293b; 
            color: #94a3b8; 
            font-weight: 600;
        }
        .heatmap-table .row-header {
            background: #1e293b; 
            color: #94a3b8;
            font-weight: 600;
            text-align: left;
        }
        .heatmap-table .cell-self { background: #1e293b; color: #475569; }
        .heatmap-table .cell-zero { background: #374151; color: #9ca3af; }
        .heatmap-table .cell-pos-weak { background: #166534; color: #fff; }
        .heatmap-table .cell-pos-strong { background: #22c55e; color: #000; font-weight: bold; }
        .heatmap-table .cell-neg-weak { background: #991b1b; color: #fff; }
        .heatmap-table .cell-neg-strong { background: #ef4444; color: #000; font-weight: bold; }
        .heatmap-table .cell-conflict { 
            background: linear-gradient(135deg, #22c55e 50%, #ef4444 50%); 
            color: #000; 
            font-weight: bold;
        }
        .heatmap-table td[title] { cursor: help; }
        .heatmap-table td:hover { opacity: 0.85; transform: scale(1.05); transition: all 0.1s; }
    </style>
    <div style="overflow-x: auto;">
    <table class="heatmap-table">
    '''
    
    # Header row
    html += '<tr><th>From \\ To</th>'
    for m in members:
        # Truncate long names
        short_name = member_names[m].split()[0][:8]
        html += f'<th title="{member_names[m]}">{short_name}</th>'
    html += '</tr>'
    
    # Data rows
    for source in members:
        short_source = member_names[source].split()[0][:8]
        html += f'<tr><td class="row-header" title="{member_names[source]}">{short_source}</td>'
        
        for target in members:
            if source == target:
                html += '<td class="cell-self">—</td>'
            else:
                # Get all channel weights for tooltip
                channel_details = []
                pos_channels = []
                neg_channels = []
                for ch in RelationshipChannel:
                    w = float(network.relations.get_weight(ch.value, source, target))
                    if w != 0:
                        sign = "+" if w > 0 else ""
                        channel_details.append(f"{ch.value.title()}: {sign}{w:.1f}")
                        if w > 0:
                            pos_channels.append(ch.value.title())
                        else:
                            neg_channels.append(ch.value.title())
                
                # Determine conflict status
                has_conflict = len(pos_channels) > 0 and len(neg_channels) > 0
                
                # Build detailed tooltip
                source_name = member_names[source]
                target_name = member_names[target]
                tooltip_lines = [f"{source_name} → {target_name}"]
                tooltip_lines.append("─" * 20)
                
                if channel_details:
                    tooltip_lines.extend(channel_details)
                else:
                    tooltip_lines.append("No active channels")
                
                tooltip_lines.append("─" * 20)
                
                if has_conflict:
                    tooltip_lines.append("⚠️ R_CONFLICT DETECTED")
                    tooltip_lines.append(f"Positive: {', '.join(pos_channels)}")
                    tooltip_lines.append(f"Negative: {', '.join(neg_channels)}")
                elif pos_channels:
                    tooltip_lines.append("✓ R_harmony (all positive)")
                elif neg_channels:
                    tooltip_lines.append("✓ R_harmony (all negative)")
                
                tooltip = "&#10;".join(tooltip_lines)  # &#10; is newline in HTML title
                
                if view_option == "Aggregate":
                    weight = float(network.relations.aggregate_weight(source, target))
                else:
                    channel = view_option.lower()
                    weight = float(network.relations.get_weight(channel, source, target))
                
                # Determine cell class based on weight and conflict
                if has_conflict and view_option == "Aggregate":
                    cell_class = "cell-conflict"
                    display = f"{weight:+.1f}⚡"
                elif weight == 0:
                    cell_class = "cell-zero"
                    display = "·"
                elif weight > 0.5:
                    cell_class = "cell-pos-strong"
                    display = f"+{weight:.1f}"
                elif weight > 0:
                    cell_class = "cell-pos-weak"
                    display = f"+{weight:.1f}"
                elif weight < -0.5:
                    cell_class = "cell-neg-strong"
                    display = f"{weight:.1f}"
                else:
                    cell_class = "cell-neg-weak"
                    display = f"{weight:.1f}"
                
                html += f'<td class="{cell_class}" title="{tooltip}">{display}</td>'
        
        html += '</tr>'
    
    html += '</table></div>'
    
    st.markdown(html, unsafe_allow_html=True)
    
    st.markdown("""
    **Legend:** 
    🟩 Strong + (>0.5) | 🟢 Weak + (0-0.5) | ⬜ Zero | 🔴 Weak - (0 to -0.5) | 🟥 Strong - (<-0.5) | ⚡ Conflict (mixed signals)
    """)


def render_conflicts(conflicts: List[ConflictReport], members: Dict[str, TeamMember]):
    """Render conflict analysis."""
    st.header("⚡ Conflict Analysis")
    
    st.markdown("""
    <div class="formal-note">
    <span class="verified-badge">FORMALLY DEFINED</span>
    <strong>Conflict</strong> = relationship with BOTH positive AND negative channels.
    </div>
    """, unsafe_allow_html=True)
    
    if not conflicts:
        st.success("✅ No conflicts detected. All relationships have consistent signals.")
        return
    
    st.warning(f"**{len(conflicts)} conflicts detected**")
    
    col1, col2, col3 = st.columns(3)
    high = [c for c in conflicts if c.severity == "high"]
    medium = [c for c in conflicts if c.severity == "medium"]
    low = [c for c in conflicts if c.severity == "low"]
    
    with col1:
        st.metric("🔴 High", len(high))
    with col2:
        st.metric("🟡 Medium", len(medium))
    with col3:
        st.metric("🟢 Low", len(low))
    
    for severity_list, severity_name, css_class in [
        (high, "High", "conflict-high"),
        (medium, "Medium", "conflict-medium"),
        (low, "Low", "conflict-low")
    ]:
        if severity_list:
            st.subheader(f"{'🔴' if severity_name == 'High' else '🟡' if severity_name == 'Medium' else '🟢'} {severity_name} Severity")
            for c in severity_list:
                source_name = members[c.source_id].name if c.source_id in members else c.source_id
                target_name = members[c.target_id].name if c.target_id in members else c.target_id
                st.markdown(f'<div class="{css_class}"><strong>{source_name} → {target_name}</strong><br>{c.description}</div>', unsafe_allow_html=True)


def render_isolation(isolated: List[IsolationReport]):
    """Render isolation analysis."""
    st.header("🏝️ Isolation Analysis")
    
    st.markdown("""
    <div class="formal-note">
    <span class="verified-badge">FORMALLY DEFINED</span>
    <strong>Isolation</strong> = violation of seriality (member has no connections).
    </div>
    """, unsafe_allow_html=True)
    
    if not isolated:
        st.success("✅ No isolated members. Everyone has connections.")
        return
    
    st.warning(f"**{len(isolated)} potentially isolated members**")
    
    for i in isolated:
        st.markdown(f'<div class="isolation-warning"><strong>{i.member_name}</strong> (ID: {i.member_id})<br>Incoming: {i.incoming_count} | Outgoing: {i.outgoing_count}<br><em>{i.recommendation}</em></div>', unsafe_allow_html=True)


def render_relationship_matrix(network: OrganizationalNetwork):
    """Render relationship matrix."""
    st.header("🔗 Relationship Matrix")
    
    if not network.members:
        show_info("Add team members to see the relationship matrix")
        return
    
    channel = st.selectbox("Select Channel", [c.value for c in RelationshipChannel], key="matrix_channel")
    
    members = list(network.members.keys())
    
    matrix_data = []
    for source in members:
        row = {"From": network.members[source].name}
        for target in members:
            if source == target:
                row[network.members[target].name] = "—"
            else:
                weight = network.relations.get_weight(channel, source, target)
                if weight == 0:
                    row[network.members[target].name] = "·"
                elif weight > 0:
                    row[network.members[target].name] = f"+{float(weight):.1f}"
                else:
                    row[network.members[target].name] = f"{float(weight):.1f}"
        matrix_data.append(row)
    
    df = pd.DataFrame(matrix_data)
    df = df.set_index("From")
    
    st.dataframe(df, use_container_width=True)
    st.caption("Positive = cooperative | Negative = antagonistic | · = no relation")


def render_relationship_details(network: OrganizationalNetwork):
    """Render detailed relationship analysis."""
    st.header("🔍 Relationship Details")
    
    members = list(network.members.keys())
    if len(members) < 2:
        show_info("Add at least 2 team members to view relationship details.")
        return
    
    col1, col2 = st.columns(2)
    with col1:
        source = st.selectbox("From", members, format_func=lambda x: network.members[x].name, key="detail_source")
    with col2:
        target_options = [m for m in members if m != source]
        target = st.selectbox("To", target_options, format_func=lambda x: network.members[x].name, key="detail_target")
    
    st.markdown("---")
    
    source_name = network.members[source].name
    target_name = network.members[target].name
    
    st.subheader(f"{source_name} → {target_name}")
    
    channel_data = []
    for ch in RelationshipChannel:
        weight = network.relations.get_weight(ch.value, source, target)
        sentiment = "🟢 Positive" if weight > 0 else "🔴 Negative" if weight < 0 else "⚪ None"
        channel_data.append({
            "Channel": ch.value.title(),
            "Weight": f"{float(weight):+.2f}" if weight != 0 else "—",
            "Sentiment": sentiment,
        })
    
    st.dataframe(pd.DataFrame(channel_data), use_container_width=True, hide_index=True)
    
    weights = {ch.value: network.relations.get_weight(ch.value, source, target) for ch in RelationshipChannel}
    has_conflict = network.relations.has_conflict(source, target)
    has_harmony = network.relations.has_harmony(source, target)
    
    col1, col2, col3 = st.columns(3)
    with col1:
        st.metric("Net Weight", f"{float(sum(weights.values())):+.2f}")
    with col2:
        st.metric("Active Channels", f"{sum(1 for w in weights.values() if w != 0)}/6")
    with col3:
        if has_conflict:
            st.metric("Status", "⚠️ CONFLICT")
        elif has_harmony and any(w != 0 for w in weights.values()):
            st.metric("Status", "✅ Harmony")
        else:
            st.metric("Status", "➖ Neutral")
    
    if has_conflict:
        pos = [ch for ch, w in weights.items() if w > 0]
        neg = [ch for ch, w in weights.items() if w < 0]
        st.markdown(f'<div class="conflict-medium"><strong>⚠️ R_conflict = TRUE</strong><br>Positive: {", ".join(pos)}<br>Negative: {", ".join(neg)}</div>', unsafe_allow_html=True)


def render_interactive_team_playground(network: OrganizationalNetwork):
    """Interactive team relations playground with live graph view."""
    st.header("🎮 Interactive Team Playground")
    
    members = list(network.members.keys())
    if len(members) < 2:
        show_info("Add at least 2 team members to use the playground.")
        return
    
    # Two-column layout like React component: Sliders | Live Graph
    col_left, col_right = st.columns([1, 1])
    
    with col_left:
        st.markdown("""
        <div class="formal-note" style="margin-bottom: 1rem;">
        <strong>Adjust relationships</strong> - Changes update the live view instantly.
        <br><em>Tip: Relations are directional (A→B ≠ B→A). Both directions are analyzed — conflicts and harmony consider how A relates to B AND how B relates to A.</em>
        </div>
        """, unsafe_allow_html=True)
        
        # Source/Target selectors
        subcol1, subcol2 = st.columns(2)
        with subcol1:
            source = st.selectbox("From", members, format_func=lambda x: network.members[x].name, key="playground_source")
        with subcol2:
            target_options = [m for m in members if m != source]
            target = st.selectbox("To", target_options, format_func=lambda x: network.members[x].name, key="playground_target")
        
        st.caption(f"**{network.members[source].name} → {network.members[target].name}**")
        
        # Channel sliders in 2 columns (compact)
        slider_cols = st.columns(2)
        weights = {}
        for i, ch in enumerate(RelationshipChannel):
            with slider_cols[i % 2]:
                slider_key = f"pg_{source}_{target}_{ch.value}"
                
                # Initialize from network if not exists
                if slider_key not in st.session_state:
                    network_val = float(network.relations.get_weight(ch.value, source, target))
                    st.session_state[slider_key] = network_val
                
                weights[ch.value] = st.slider(
                    ch.value.title(), 
                    min_value=-1.0, 
                    max_value=1.0, 
                    step=0.1, 
                    key=slider_key,
                    help=f"{ch.value}: -1 (hostile) to +1 (strong)"
                )
        
        # Real-time analysis for this pair
        pos_ch = [ch for ch, w in weights.items() if w > 0]
        neg_ch = [ch for ch, w in weights.items() if w < 0]
        
        has_conflict = len(pos_ch) > 0 and len(neg_ch) > 0
        has_harmony = len(pos_ch) > 1 and len(neg_ch) == 0
        all_negative = len(neg_ch) > 0 and len(pos_ch) == 0
        
        # Compact metrics row
        m1, m2, m3 = st.columns(3)
        with m1:
            net_val = sum(weights.values())
            st.metric("Net", f"{net_val:+.1f}", delta=None)
        with m2:
            st.metric("Active", f"{len(pos_ch) + len(neg_ch)}/6")
        with m3:
            if has_conflict:
                st.metric("Status", "⚠️ Conflict")
            elif all_negative:
                st.metric("Status", "🔴 Hostile")
            elif has_harmony:
                st.metric("Status", "✅ Harmony")
            else:
                st.metric("Status", "➖ Neutral")
        
        # Status messages
        if has_conflict:
            st.error(f"**R_conflict**: +{','.join(pos_ch)} / -{','.join(neg_ch)}")
        elif all_negative:
            st.error(f"**Hostile**: All negative ({','.join(neg_ch)})")
        elif has_harmony:
            st.success(f"**R_harmony**: {', '.join(pos_ch)}")
        
        # Reset button
        if st.button("🔄 Reset All Sliders", use_container_width=True):
            keys_to_clear = [k for k in st.session_state.keys() if k.startswith('pg_')]
            for k in keys_to_clear:
                del st.session_state[k]
            st.rerun()
    
    with col_right:
        st.markdown("### 📊 Live Network View")
        
        # Live graph visualization with per-channel colored lines
        if HAS_VISUALIZATION:
            import math
            
            # Channel colors - same as geopolitical for consistency
            channel_colors = {
                'collaboration': '#22c55e',  # Green
                'trust': '#3b82f6',          # Blue
                'influence': '#8b5cf6',      # Purple
                'communication': '#f59e0b',  # Orange
                'social': '#ec4899',         # Pink
                'reporting': '#06b6d4'       # Cyan
            }
            
            # Calculate node positions using spring layout
            import networkx as nx
            G = nx.DiGraph()
            for m in members:
                G.add_node(m)
            
            # Add edges for layout calculation
            for s in members:
                for t in members:
                    if s != t:
                        total = sum(abs(float(network.relations.get_weight(ch.value, s, t))) for ch in RelationshipChannel)
                        if total > 0:
                            G.add_edge(s, t)
            
            if len(G.edges()) > 0:
                pos = nx.spring_layout(G, k=2, iterations=50, seed=42)
            else:
                # Arrange in circle if no edges
                angle_step = 2 * math.pi / len(members)
                pos = {m: (math.cos(i * angle_step), math.sin(i * angle_step)) for i, m in enumerate(members)}
            
            # Build per-channel edge data
            edges_data = []
            
            for src in members:
                for tgt in members:
                    if src == tgt:
                        continue
                    
                    x1, y1 = pos[src]
                    x2, y2 = pos[tgt]
                    
                    dx = x2 - x1
                    dy = y2 - y1
                    length = math.sqrt(dx*dx + dy*dy) or 1
                    
                    # Perpendicular vector for spreading channels
                    perp_x = -dy / length
                    perp_y = dx / length
                    
                    # Check if reverse exists
                    has_reverse = any(float(network.relations.get_weight(ch.value, tgt, src)) != 0 for ch in RelationshipChannel)
                    base_offset = 0.015 if has_reverse else 0
                    
                    # Draw each channel
                    for ch_idx, ch in enumerate(RelationshipChannel):
                        weight = float(network.relations.get_weight(ch.value, src, tgt))
                        if weight == 0:
                            continue
                        
                        # Spread channels perpendicular to edge
                        spread = (ch_idx - 2.5) * 0.012
                        offset = base_offset + spread
                        
                        ox1 = x1 + perp_x * offset
                        oy1 = y1 + perp_y * offset
                        ox2 = x2 + perp_x * offset
                        oy2 = y2 + perp_y * offset
                        
                        # Shorten to not overlap nodes
                        shorten = 0.12
                        fx1 = ox1 + dx/length * shorten
                        fy1 = oy1 + dy/length * shorten
                        fx2 = ox2 - dx/length * shorten
                        fy2 = oy2 - dy/length * shorten
                        
                        edges_data.append({
                            'x': fx1, 'y': fy1,
                            'x2': fx2, 'y2': fy2,
                            'channel': ch.value,
                            'weight': weight,
                            'color': channel_colors[ch.value],
                            'thickness': 1 + abs(weight) * 2,
                            'source': network.members[src].name,
                            'target': network.members[tgt].name
                        })
            
            # Build node data
            nodes_data = []
            for m_id in members:
                # Check for conflicts
                has_problem = False
                for other in members:
                    if other == m_id:
                        continue
                    if network.relations.has_conflict(m_id, other) or network.relations.has_conflict(other, m_id):
                        has_problem = True
                        break
                
                nodes_data.append({
                    'id': m_id,
                    'name': network.members[m_id].name,
                    'x': pos[m_id][0],
                    'y': pos[m_id][1],
                    'color': '#ef4444' if has_problem else '#1e40af'
                })
            
            # Create Altair chart
            chart_layers = []
            
            if edges_data:
                edges_df = pd.DataFrame(edges_data)
                
                edges_chart = alt.Chart(edges_df).mark_line(
                    strokeWidth=2,
                    opacity=0.7
                ).encode(
                    x=alt.X('x:Q', axis=None, scale=alt.Scale(domain=[-1.5, 1.5])),
                    y=alt.Y('y:Q', axis=None, scale=alt.Scale(domain=[-1.5, 1.5])),
                    x2='x2:Q',
                    y2='y2:Q',
                    color=alt.Color('channel:N',
                                   scale=alt.Scale(
                                       domain=list(channel_colors.keys()),
                                       range=list(channel_colors.values())
                                   ),
                                   legend=None),
                    strokeWidth=alt.StrokeWidth('thickness:Q', scale=None, legend=None),
                    strokeDash=alt.condition(
                        alt.datum.weight < 0,
                        alt.value([4, 2]),
                        alt.value([])
                    ),
                    tooltip=['source:N', 'target:N', 'channel:N', 'weight:Q']
                )
                chart_layers.append(edges_chart)
            
            # Nodes
            nodes_df = pd.DataFrame(nodes_data)
            
            # Create initials (first letter of each word)
            def get_initials(name):
                parts = name.split()
                if len(parts) >= 2:
                    return (parts[0][0] + parts[1][0]).upper()
                return name[:2].upper()
            
            # Build unique display names
            all_names = list(nodes_df['name'])
            display_names = {}
            
            for name in all_names:
                parts = str(name).split()
                first = parts[0] if parts else str(name)
                last = parts[-1] if len(parts) > 1 else ""
                
                # Start with just first name
                display = first
                
                # Check if unique
                others_with_same = [n for n in all_names if n != name and str(n).split()[0] == first]
                
                if others_with_same and last:
                    # Try "First L."
                    display = f"{first} {last[0]}."
                    
                    # Check if still duplicate
                    for other in others_with_same:
                        other_parts = str(other).split()
                        other_last = other_parts[-1] if len(other_parts) > 1 else ""
                        if other_last and other_last[0] == last[0]:
                            # Same first name and last initial - use more of last name
                            for length in range(2, len(last) + 1):
                                display = f"{first} {last[:length]}."
                                conflict = False
                                for o in others_with_same:
                                    o_parts = str(o).split()
                                    o_last = o_parts[-1] if len(o_parts) > 1 else ""
                                    if o_last[:length] == last[:length]:
                                        conflict = True
                                        break
                                if not conflict:
                                    break
                            else:
                                # Last resort: full name
                                display = name
                            break
                
                display_names[name] = display
            
            nodes_df['initials'] = nodes_df['name'].apply(get_initials)
            nodes_df['short_name'] = nodes_df['name'].apply(lambda x: display_names.get(x, x))
            
            nodes_chart = alt.Chart(nodes_df).mark_circle(
                size=1800,  # Bigger circles
                stroke='white',
                strokeWidth=2
            ).encode(
                x='x:Q',
                y='y:Q',
                color=alt.Color('color:N', scale=None, legend=None),
                tooltip=['name:N']
            )
            chart_layers.append(nodes_chart)
            
            # Initials inside circle
            initials_chart = alt.Chart(nodes_df).mark_text(
                fontSize=12,
                fontWeight='bold'
            ).encode(
                x='x:Q',
                y='y:Q',
                text='initials:N',
                color=alt.value('white')
            )
            chart_layers.append(initials_chart)
            
            # First name below circle (with disambiguation if needed)
            labels_chart = alt.Chart(nodes_df).mark_text(
                fontSize=10,
                dy=32  # Position below circle
            ).encode(
                x='x:Q',
                y='y:Q',
                text='short_name:N',
                color=alt.value('#374151')
            )
            chart_layers.append(labels_chart)
            
            if chart_layers:
                chart = alt.layer(*chart_layers).properties(
                    width=380,
                    height=300
                ).configure_view(strokeWidth=0)
                
                st.altair_chart(chart, use_container_width=True)
            else:
                show_info("Add relationships to see the graph")
            
            # Legend
            st.markdown("""
            <div style="background: #f8fafc; border: 1px solid #e2e8f0; padding: 8px; border-radius: 6px; font-size: 11px; color: #1f2937;">
            <strong>Channels:</strong>
            <span style="color: #22c55e;">━</span> Collab
            <span style="color: #3b82f6;">━</span> Trust
            <span style="color: #8b5cf6;">━</span> Influence
            <span style="color: #f59e0b;">━</span> Comm
            <span style="color: #ec4899;">━</span> Social
            <span style="color: #06b6d4;">━</span> Report<br>
            <strong>Style:</strong> Solid=Positive | Dashed=Negative | 🔵OK | 🔴Conflict
            </div>
            """, unsafe_allow_html=True)
        else:
            st.info("Install networkx, altair for visualization")
        
        # Network-wide stats (like React component)
        # These recalculate fresh on every run from the synced network
        conflicts = network.detect_conflicts()
        hostile = network.detect_hostile()
        
        # Build harmony list (relationships with multiple positive channels, no negative)
        harmonies_list = []
        for s in members:
            for t in members:
                if s >= t:
                    continue
                pos_channels = []
                neg_channels = []
                for ch in RelationshipChannel:
                    w1 = float(network.relations.get_weight(ch.value, s, t))
                    w2 = float(network.relations.get_weight(ch.value, t, s))
                    if w1 > 0 or w2 > 0:
                        pos_channels.append(ch.value)
                    if w1 < 0 or w2 < 0:
                        neg_channels.append(ch.value)
                if len(pos_channels) > 1 and len(neg_channels) == 0:
                    harmonies_list.append({
                        'from': s, 'to': t,
                        'from_name': network.members[s].name,
                        'to_name': network.members[t].name,
                        'channels': pos_channels
                    })
        
        # Stats cards - these update live when sliders change
        st.markdown("---")
        
        # Show sync indicator
        slider_keys = [k for k in st.session_state.keys() if k.startswith('pg_')]
        if slider_keys:
            modified_count = len(slider_keys)
            st.success(f"🔄 **Live stats** — {modified_count} channel values tracked")
        
        s1, s2, s3, s4 = st.columns(4)
        with s1:
            st.metric("Nodes", len(members))
        with s2:
            edge_count = sum(1 for s in members for t in members if s != t 
                           for ch in RelationshipChannel 
                           if float(network.relations.get_weight(ch.value, s, t)) != 0)
            st.metric("Edges", edge_count)
        with s3:
            st.metric("R_conflict", len(conflicts), delta="⚠️" if conflicts else None, delta_color="inverse")
        with s4:
            st.metric("R_harmony", len(harmonies_list))
        
        # Show hostile metric
        if hostile:
            st.metric("Hostile", len(hostile), delta="🔴", delta_color="inverse")
        
        # Expandable details for conflicts
        if conflicts:
            with st.expander(f"⚠️ **View {len(conflicts)} R_conflict Details** (mixed signals)", expanded=False):
                for c in conflicts:
                    src_name = network.members[c.source_id].name if c.source_id in network.members else c.source_id
                    tgt_name = network.members[c.target_id].name if c.target_id in network.members else c.target_id
                    st.markdown(f"""
                    <div style="background: #fef2f2; border: 2px solid #ef4444; padding: 12px; border-radius: 8px; margin-bottom: 10px; color: #1f2937;">
                    <strong style="color: #b91c1c; font-size: 14px;">{src_name} → {tgt_name}</strong><br>
                    <span style="color: #6b7280;">{c.description}</span><br>
                    <span style="color: #15803d;">✓ Positive:</span> <strong>{', '.join(c.positive_channels)}</strong><br>
                    <span style="color: #dc2626;">✗ Negative:</span> <strong>{', '.join(c.negative_channels)}</strong>
                    </div>
                    """, unsafe_allow_html=True)
        
        # Expandable details for hostile
        if hostile:
            with st.expander(f"🔴 **View {len(hostile)} Hostile Details** (all negative)", expanded=False):
                for h in hostile:
                    src_name = network.members[h.source_id].name if h.source_id in network.members else h.source_id
                    tgt_name = network.members[h.target_id].name if h.target_id in network.members else h.target_id
                    st.markdown(f"""
                    <div style="background: #fef2f2; border: 2px solid #991b1b; padding: 12px; border-radius: 8px; margin-bottom: 10px; color: #1f2937;">
                    <strong style="color: #991b1b; font-size: 14px;">{src_name} → {tgt_name}</strong><br>
                    <span style="color: #dc2626;">⚠ Hostile channels:</span> <strong>{', '.join(h.negative_channels)}</strong><br>
                    <span style="color: #6b7280;">Total weight: {h.total_weight:.1f}</span>
                    </div>
                    """, unsafe_allow_html=True)
        
        # Expandable details for harmony
        if harmonies_list:
            with st.expander(f"✅ **View {len(harmonies_list)} R_harmony Details** (aligned)", expanded=False):
                for h in harmonies_list:
                    st.markdown(f"""
                    <div style="background: #f0fdf4; border: 2px solid #22c55e; padding: 12px; border-radius: 8px; margin-bottom: 10px; color: #1f2937;">
                    <strong style="color: #15803d; font-size: 14px;">{h['from_name']} ↔ {h['to_name']}</strong><br>
                    <span style="color: #15803d;">✓ Aligned channels:</span> <strong>{', '.join(h['channels'])}</strong>
                    </div>
                    """, unsafe_allow_html=True)
        
        # Current health score
        report = network.generate_health_report()
        health = report.overall_health_score()
        health_color = "🟢" if health >= 70 else "🟡" if health >= 50 else "🔴"
        st.markdown(f"### {health_color} Health Score: **{health:.0f}/100**")


def render_team_members(network: OrganizationalNetwork):
    """Render team members list."""
    st.header("👥 Team Members")
    
    if not network.members:
        show_info("No team members yet. Use the sidebar to add members.")
        return
    
    data = []
    for m_id, member in network.members.items():
        out_count = len([t for t in network.members if t != m_id and network.relations.aggregate_weight(m_id, t) != 0])
        in_count = len([s for s in network.members if s != m_id and network.relations.aggregate_weight(s, m_id) != 0])
        data.append({"ID": m_id, "Name": member.name, "Role": member.role, "Department": member.department, "Outgoing": out_count, "Incoming": in_count})
    
    st.dataframe(pd.DataFrame(data), use_container_width=True, hide_index=True)


def render_geopolitical_playground():
    """Render geopolitical playground with live network visualization."""
    st.header("🌍 Geopolitical Playground")
    
    st.markdown('<div class="formal-note"><strong>Preview:</strong> Same UCF/GUTT relational mathematics applied to nation-level analysis. Adjust relations and see real-time conflict/harmony detection.</div>', unsafe_allow_html=True)
    
    nations = {
        "USA": "United States", 
        "CHN": "China", 
        "RUS": "Russia", 
        "EUR": "European Union",
        "IND": "India"
    }
    channels = ["trade", "military", "diplomatic", "intelligence", "cultural", "resource"]
    
    # Initialize geopolitical weights
    if 'geo_weights' not in st.session_state:
        st.session_state.geo_weights = {}
        for n1 in nations:
            for n2 in nations:
                if n1 != n2:
                    st.session_state.geo_weights[(n1, n2)] = {ch: 0.0 for ch in channels}
        # Set some realistic starting values
        st.session_state.geo_weights[("USA", "EUR")] = {"trade": 0.8, "military": 0.9, "diplomatic": 0.7, "intelligence": 0.8, "cultural": 0.7, "resource": 0.5}
        st.session_state.geo_weights[("EUR", "USA")] = {"trade": 0.8, "military": 0.7, "diplomatic": 0.8, "intelligence": 0.6, "cultural": 0.8, "resource": 0.4}
        st.session_state.geo_weights[("USA", "CHN")] = {"trade": 0.6, "military": -0.5, "diplomatic": 0.2, "intelligence": -0.7, "cultural": 0.3, "resource": -0.3}
        st.session_state.geo_weights[("CHN", "USA")] = {"trade": 0.7, "military": -0.4, "diplomatic": 0.1, "intelligence": -0.6, "cultural": 0.2, "resource": -0.2}
        st.session_state.geo_weights[("USA", "RUS")] = {"trade": -0.3, "military": -0.7, "diplomatic": -0.4, "intelligence": -0.8, "cultural": 0.1, "resource": -0.5}
        st.session_state.geo_weights[("RUS", "USA")] = {"trade": -0.2, "military": -0.6, "diplomatic": -0.5, "intelligence": -0.7, "cultural": 0.0, "resource": -0.4}
        st.session_state.geo_weights[("CHN", "RUS")] = {"trade": 0.5, "military": 0.4, "diplomatic": 0.6, "intelligence": 0.3, "cultural": 0.2, "resource": 0.7}
        st.session_state.geo_weights[("RUS", "CHN")] = {"trade": 0.6, "military": 0.5, "diplomatic": 0.5, "intelligence": 0.4, "cultural": 0.3, "resource": 0.8}
        st.session_state.geo_weights[("IND", "USA")] = {"trade": 0.5, "military": 0.4, "diplomatic": 0.6, "intelligence": 0.3, "cultural": 0.5, "resource": 0.3}
    
    # Two-column layout like team playground
    col_left, col_right = st.columns([1, 1])
    
    with col_left:
        st.markdown("### Adjust Relations")
        st.caption("💡 Relations are directional — USA→CHN ≠ CHN→USA. Both directions matter: how USA relates to CHN AND how CHN relates to USA.")
        
        subcol1, subcol2 = st.columns(2)
        with subcol1:
            source = st.selectbox("From Nation", list(nations.keys()), format_func=lambda x: f"{x} - {nations[x]}", key="geo_source")
        with subcol2:
            target_opts = [n for n in nations if n != source]
            target = st.selectbox("To Nation", target_opts, format_func=lambda x: f"{x} - {nations[x]}", key="geo_target")
        
        st.caption(f"**{nations[source]} → {nations[target]}**")
        
        pair_key = (source, target)
        weights = st.session_state.geo_weights.get(pair_key, {ch: 0.0 for ch in channels})
        
        # Channel sliders in 2 columns
        slider_cols = st.columns(2)
        for i, ch in enumerate(channels):
            with slider_cols[i % 2]:
                slider_key = f"geo_{source}_{target}_{ch}"
                new_val = st.slider(
                    ch.title(), 
                    -1.0, 1.0, 
                    float(weights.get(ch, 0.0)), 
                    0.1, 
                    key=slider_key,
                    help=f"{ch}: -1 (hostile) to +1 (allied)"
                )
                st.session_state.geo_weights[pair_key][ch] = new_val
        
        # Real-time analysis for this pair
        weights = st.session_state.geo_weights[pair_key]
        pos_ch = [ch for ch, w in weights.items() if w > 0]
        neg_ch = [ch for ch, w in weights.items() if w < 0]
        
        has_conflict = len(pos_ch) > 0 and len(neg_ch) > 0
        has_harmony = len(pos_ch) > 1 and len(neg_ch) == 0
        all_negative = len(neg_ch) > 0 and len(pos_ch) == 0
        
        # Compact metrics
        m1, m2, m3 = st.columns(3)
        with m1:
            net_val = sum(weights.values())
            st.metric("Net", f"{net_val:+.1f}")
        with m2:
            st.metric("Active", f"{len(pos_ch) + len(neg_ch)}/6")
        with m3:
            if has_conflict:
                st.metric("Status", "⚠️ Complex")
            elif all_negative:
                st.metric("Status", "🔴 Hostile")
            elif has_harmony:
                st.metric("Status", "✅ Allied")
            else:
                st.metric("Status", "➖ Neutral")
        
        if has_conflict:
            st.error(f"**R_conflict**: Cooperative in {','.join(pos_ch)} but competitive in {','.join(neg_ch)}")
        elif all_negative:
            st.error(f"**Adversarial**: All channels negative ({','.join(neg_ch)})")
        elif has_harmony:
            st.success(f"**R_harmony**: Allied across {', '.join(pos_ch)}")
        
        # Reset button
        if st.button("🔄 Reset Geopolitical Data", use_container_width=True):
            del st.session_state.geo_weights
            st.rerun()
    
    with col_right:
        st.markdown("### 📊 Live Geopolitical Network")
        
        # Build geopolitical network visualization
        if HAS_VISUALIZATION:
            import math
            
            # Channel colors - distinct and colorblind-friendly
            channel_colors = {
                'trade': '#22c55e',       # Green - money/commerce
                'military': '#ef4444',    # Red - conflict/defense
                'diplomatic': '#3b82f6',  # Blue - formal relations
                'intelligence': '#8b5cf6', # Purple - covert
                'cultural': '#f59e0b',    # Orange/Amber - soft power
                'resource': '#06b6d4'     # Cyan - commodities
            }
            
            # Fixed positions for stability
            pos = {
                'USA': (-0.85, 0.2),
                'EUR': (0.0, 0.85),
                'CHN': (0.85, 0.2),
                'RUS': (0.5, -0.6),
                'IND': (-0.5, -0.6)
            }
            
            # Build per-channel edge data
            edges_data = []
            
            for (src, tgt), ch_weights in st.session_state.geo_weights.items():
                x1, y1 = pos[src]
                x2, y2 = pos[tgt]
                
                # Calculate direction vector
                dx = x2 - x1
                dy = y2 - y1
                length = math.sqrt(dx*dx + dy*dy) or 1
                
                # Perpendicular vector for spreading channels
                perp_x = -dy / length
                perp_y = dx / length
                
                # Check if reverse exists (for directional offset)
                has_reverse = (tgt, src) in st.session_state.geo_weights
                base_offset = 0.02 if has_reverse else 0
                
                # Draw each channel as separate line
                for ch_idx, (ch, weight) in enumerate(ch_weights.items()):
                    if weight == 0:
                        continue
                    
                    # Spread channels perpendicular to edge
                    # 6 channels spread from -0.05 to +0.05
                    spread = (ch_idx - 2.5) * 0.018
                    offset = base_offset + spread
                    
                    # Offset points
                    ox1 = x1 + perp_x * offset
                    oy1 = y1 + perp_y * offset
                    ox2 = x2 + perp_x * offset
                    oy2 = y2 + perp_y * offset
                    
                    # Shorten to not overlap nodes
                    shorten = 0.14
                    fx1 = ox1 + dx/length * shorten
                    fy1 = oy1 + dy/length * shorten
                    fx2 = ox2 - dx/length * shorten
                    fy2 = oy2 - dy/length * shorten
                    
                    # Line thickness based on absolute weight
                    thickness = 1 + abs(weight) * 2
                    
                    # Opacity: solid for positive, lighter for negative
                    opacity = 0.9 if weight > 0 else 0.5
                    
                    edges_data.append({
                        'x': fx1, 'y': fy1,
                        'x2': fx2, 'y2': fy2,
                        'channel': ch,
                        'weight': weight,
                        'color': channel_colors[ch],
                        'thickness': thickness,
                        'opacity': opacity,
                        'dash': '4,2' if weight < 0 else '',
                        'source': src,
                        'target': tgt
                    })
            
            # Build node data
            nodes_data = []
            for nation_id in nations:
                # Check for conflicts
                has_problem = False
                for other in nations:
                    if other == nation_id:
                        continue
                    w1 = st.session_state.geo_weights.get((nation_id, other), {})
                    w2 = st.session_state.geo_weights.get((other, nation_id), {})
                    for w in [w1, w2]:
                        pos_chs = [c for c, v in w.items() if v > 0]
                        neg_chs = [c for c, v in w.items() if v < 0]
                        if len(pos_chs) > 0 and len(neg_chs) > 0:
                            has_problem = True
                            break
                    if has_problem:
                        break
                
                nodes_data.append({
                    'id': nation_id,
                    'name': nations[nation_id],
                    'x': pos[nation_id][0],
                    'y': pos[nation_id][1],
                    'color': '#ef4444' if has_problem else '#1e40af'
                })
            
            # Create Altair chart
            chart_layers = []
            
            if edges_data:
                edges_df = pd.DataFrame(edges_data)
                
                # Draw edges grouped by channel for proper coloring
                edges_chart = alt.Chart(edges_df).mark_line(
                    strokeWidth=2,
                    opacity=0.7
                ).encode(
                    x=alt.X('x:Q', axis=None, scale=alt.Scale(domain=[-1.3, 1.3])),
                    y=alt.Y('y:Q', axis=None, scale=alt.Scale(domain=[-1.0, 1.2])),
                    x2='x2:Q',
                    y2='y2:Q',
                    color=alt.Color('channel:N', 
                                   scale=alt.Scale(
                                       domain=list(channel_colors.keys()),
                                       range=list(channel_colors.values())
                                   ),
                                   legend=alt.Legend(title='Channel', orient='right')),
                    strokeWidth=alt.StrokeWidth('thickness:Q', scale=None, legend=None),
                    strokeDash=alt.condition(
                        alt.datum.weight < 0,
                        alt.value([4, 2]),
                        alt.value([])
                    ),
                    tooltip=['source:N', 'target:N', 'channel:N', 'weight:Q']
                )
                chart_layers.append(edges_chart)
            
            # Nodes
            nodes_df = pd.DataFrame(nodes_data)
            nodes_chart = alt.Chart(nodes_df).mark_circle(
                size=1400, 
                stroke='white', 
                strokeWidth=2
            ).encode(
                x='x:Q', 
                y='y:Q',
                color=alt.Color('color:N', scale=None, legend=None),
                tooltip=['name:N']
            )
            chart_layers.append(nodes_chart)
            
            # Node labels - ID inside circle, full name below
            id_labels = alt.Chart(nodes_df).mark_text(
                fontSize=12, 
                fontWeight='bold'
            ).encode(
                x='x:Q', 
                y='y:Q', 
                text='id:N',
                color=alt.value('white')
            )
            chart_layers.append(id_labels)
            
            # Full name below circle
            name_labels = alt.Chart(nodes_df).mark_text(
                fontSize=10,
                dy=40
            ).encode(
                x='x:Q',
                y='y:Q',
                text='name:N',
                color=alt.value('#1f2937')
            )
            chart_layers.append(name_labels)
            
            # Combine layers
            if chart_layers:
                chart = alt.layer(*chart_layers).properties(
                    width=420, 
                    height=350
                ).configure_view(strokeWidth=0)
                
                st.altair_chart(chart, use_container_width=True)
            
            # Legend explanation
            st.markdown("""
            <div style="background: #1e293b; padding: 10px; border-radius: 8px; font-size: 12px;">
            <strong>Channel Legend:</strong><br>
            <span style="color: #22c55e;">━━</span> Trade &nbsp;
            <span style="color: #ef4444;">━━</span> Military &nbsp;
            <span style="color: #3b82f6;">━━</span> Diplomatic<br>
            <span style="color: #8b5cf6;">━━</span> Intelligence &nbsp;
            <span style="color: #f59e0b;">━━</span> Cultural &nbsp;
            <span style="color: #06b6d4;">━━</span> Resource<br>
            <strong>Line Style:</strong> Solid = Positive | Dashed = Negative<br>
            <strong>Thickness:</strong> Stronger weight = thicker line<br>
            <strong>Nodes:</strong> 🔵 OK | 🔴 Has R_conflict (mixed signals)
            </div>
            """, unsafe_allow_html=True)
        else:
            st.info("Install altair for visualization")
        
        # Network-wide stats
        st.markdown("---")
        # Show sync indicator
        geo_keys = [k for k in st.session_state.keys() if k.startswith('geo_') and '_' in k[4:]]
        if geo_keys:
            st.success(f"🔄 **Live stats** — {len(geo_keys)} channel values tracked")
        
        # Collect detailed conflict and hostile information (FRESH on every rerun)
        conflicts_list = []
        harmonies_list = []
        hostile_list = []
        
        for (src, tgt), w in st.session_state.geo_weights.items():
            pos_chs = [(c, v) for c, v in w.items() if v > 0]
            neg_chs = [(c, v) for c, v in w.items() if v < 0]
            
            if len(pos_chs) > 0 and len(neg_chs) > 0:
                conflicts_list.append({
                    'from': src, 'to': tgt,
                    'from_name': nations[src], 'to_name': nations[tgt],
                    'positive': pos_chs, 'negative': neg_chs
                })
            elif len(pos_chs) > 1:
                harmonies_list.append({
                    'from': src, 'to': tgt,
                    'from_name': nations[src], 'to_name': nations[tgt],
                    'channels': pos_chs
                })
            elif len(neg_chs) > 0 and len(pos_chs) == 0:
                hostile_list.append({
                    'from': src, 'to': tgt,
                    'from_name': nations[src], 'to_name': nations[tgt],
                    'channels': neg_chs
                })
        
        s1, s2, s3, s4 = st.columns(4)
        with s1:
            st.metric("Nations", len(nations))
        with s2:
            st.metric("R_conflict", len(conflicts_list), delta="⚠️" if conflicts_list else None, delta_color="inverse")
        with s3:
            st.metric("R_harmony", len(harmonies_list))
        with s4:
            st.metric("Hostile", len(hostile_list), delta="🔴" if hostile_list else None, delta_color="inverse")
        
        # Expandable details for conflicts (content updates on each rerun)
        if conflicts_list:
            with st.expander(f"⚠️ **View {len(conflicts_list)} R_conflict Details** (mixed signals)", expanded=False):
                for c in conflicts_list:
                    pos_str = ', '.join([f"{ch} ({v:+.1f})" for ch, v in c['positive']])
                    neg_str = ', '.join([f"{ch} ({v:+.1f})" for ch, v in c['negative']])
                    st.markdown(f"""
                    <div style="background: #fef2f2; border: 2px solid #ef4444; padding: 12px; border-radius: 8px; margin-bottom: 10px; color: #1f2937;">
                    <strong style="color: #b91c1c; font-size: 14px;">{c['from']} → {c['to']}</strong> 
                    <span style="color: #6b7280;">({c['from_name']} → {c['to_name']})</span><br>
                    <span style="color: #15803d;">✓ Cooperative:</span> <strong>{pos_str}</strong><br>
                    <span style="color: #dc2626;">✗ Competitive:</span> <strong>{neg_str}</strong>
                    </div>
                    """, unsafe_allow_html=True)
        
        # Expandable details for hostile
        if hostile_list:
            with st.expander(f"🔴 **View {len(hostile_list)} Hostile Details** (all negative)", expanded=False):
                for h in hostile_list:
                    ch_str = ', '.join([f"{ch} ({v:+.1f})" for ch, v in h['channels']])
                    total = sum(v for ch, v in h['channels'])
                    st.markdown(f"""
                    <div style="background: #fef2f2; border: 2px solid #991b1b; padding: 12px; border-radius: 8px; margin-bottom: 10px; color: #1f2937;">
                    <strong style="color: #991b1b; font-size: 14px;">{h['from']} → {h['to']}</strong>
                    <span style="color: #6b7280;">({h['from_name']} → {h['to_name']})</span><br>
                    <span style="color: #dc2626;">⚠ Hostile channels:</span> <strong>{ch_str}</strong><br>
                    <span style="color: #6b7280;">Total: {total:+.1f}</span>
                    </div>
                    """, unsafe_allow_html=True)
        
        # Expandable details for harmony
        if harmonies_list:
            with st.expander(f"✅ **View {len(harmonies_list)} R_harmony Details** (allied)", expanded=False):
                for h in harmonies_list:
                    ch_str = ', '.join([f"{ch} ({v:+.1f})" for ch, v in h['channels']])
                    total = sum(v for ch, v in h['channels'])
                    st.markdown(f"""
                    <div style="background: #f0fdf4; border: 2px solid #22c55e; padding: 12px; border-radius: 8px; margin-bottom: 10px; color: #1f2937;">
                    <strong style="color: #15803d; font-size: 14px;">{h['from']} → {h['to']}</strong>
                    <span style="color: #6b7280;">({h['from_name']} → {h['to_name']})</span><br>
                    <span style="color: #15803d;">✓ Allied channels:</span> <strong>{ch_str}</strong><br>
                    <span style="color: #6b7280;">Total: {total:+.1f}</span>
                    </div>
                    """, unsafe_allow_html=True)
        
        # Overall assessment
        if len(conflicts_list) > 3:
            st.error(f"🌐 **High Tension**: {len(conflicts_list)} complex relationships detected")
        elif len(hostile_list) > 2:
            st.warning(f"🌐 **Adversarial Climate**: {len(hostile_list)} hostile relationships")
        elif len(harmonies_list) > 3:
            st.success(f"🌐 **Stable Order**: {len(harmonies_list)} allied relationships")
        else:
            st.info("🌐 **Mixed Landscape**: Varied relationship dynamics")


def render_formal_basis():
    """Render formal basis explanation."""
    st.header("📜 Formal Mathematical Basis")
    
    with st.expander("⚠️ Demo vs Licensed Capabilities"):
        st.markdown("""
        ### Demo Includes
        - 25+ Polinode-style network metrics
        - UCF/GUTT predicates (R_conflict, R_harmony)
        - Seriality checking (Proposition 01)
        - Network visualization
        - Multiple sample datasets
        
        ### Licensed Version Adds
        - 21,221+ lines of Coq proofs
        - Verified OCaml extraction
        - Nested Relational Tensors (NRT)
        - Temporal tracking
        - Commercial use rights
        
        **Contact:** relationalexistence.com
        """)
    
    with st.expander("Key Theorems (from Coq)"):
        st.code("""
(* R_conflict: positive AND negative channels *)
Definition R_conflict M channels a b :=
  (exists k1, In k1 channels /\\ R_pos (M k1) a b) /\\
  (exists k2, In k2 channels /\\ R_neg (M k2) a b).

(* Seriality: every entity has outgoing edge *)
Theorem proposition_01 : forall x, exists y, R x y.
        """, language="coq")


def main():
    """Main application."""
    render_header()
    render_sidebar()
    
    if 'network' not in st.session_state or not st.session_state.get('data_loaded', False):
        st.info("👈 Use the sidebar to load a sample dataset or add team members")
        
        st.markdown("### Available Sample Datasets")
        datasets = get_sample_datasets()
        for name in datasets.keys():
            st.write(f"• {name}")
        
        st.markdown("---")
        render_formal_basis()
        return
    
    network = st.session_state.network
    
    # ALWAYS sync playground slider values to network before rendering ANY tab
    # This reads directly from slider session_state keys (pg_source_target_channel)
    synced = sync_playground_to_network(network)
    st.session_state.network = network
    
    # Generate fresh report with current (synced) network state
    report = network.generate_health_report()
    
    # Store report in session state so we can verify it updates
    st.session_state.current_report = report
    
    # Create tabs with new metrics tabs
    tabs = st.tabs([
        "📈 Overview", 
        "📊 Metrics (25+)",
        "🔲 Heatmap",
        "⚡ Conflicts", 
        "🏝️ Isolation",
        "🔗 Matrix",
        "🔍 Details",
        "🎮 Playground",
        "👥 Team",
        "🌍 Geopolitical",
        "📜 Formal Basis"
    ])
    
    with tabs[0]:
        render_metrics(report)
    
    with tabs[1]:
        render_polinode_metrics(network)
    
    with tabs[2]:
        render_heatmap_matrix(network)
    
    with tabs[3]:
        render_conflicts(report.conflicts, network.members)
    
    with tabs[4]:
        render_isolation(report.isolated_members)
    
    with tabs[5]:
        render_relationship_matrix(network)
    
    with tabs[6]:
        render_relationship_details(network)
    
    with tabs[7]:
        render_interactive_team_playground(network)
    
    with tabs[8]:
        render_team_members(network)
    
    with tabs[9]:
        render_geopolitical_playground()
    
    with tabs[10]:
        render_formal_basis()
    
    # Footer
    st.markdown("---")
    st.markdown("""
    <div style="text-align: center; color: #666; font-size: 0.9em;">
    UCF/GUTT™ ONA Analyzer — <strong>Enhanced Demo (25+ Metrics)</strong><br>
    © 2023-2026 Michael Fillippini. All Rights Reserved.<br>
    <a href="https://relationalexistence.com">License full version</a>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    main()
