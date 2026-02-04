"""
UCF/GUTT Audit Framework - Streamlit Application
================================================

DEMONSTRATION VERSION - Simplified algorithms for concept illustration.
Production system uses proprietary UCF/GUTT tensor analysis.

Copyright (c) 2026 Michael Fillippini. All Rights Reserved.
"""

import streamlit as st
import pandas as pd
import plotly.express as px
import plotly.graph_objects as go
import networkx as nx
import streamlit.components.v1 as components
from typing import Dict, List
from decimal import Decimal
from datetime import date
import tempfile
import os

# Optional pyvis import
try:
    from pyvis.network import Network
    PYVIS_AVAILABLE = True
    print("✓ pyvis loaded successfully")
except ImportError as e:
    PYVIS_AVAILABLE = False
    print(f"✗ pyvis not available: {e}")

from audit_core import (
    AuditUniverse, AuditFinding, TransactionDomain, 
    SOXControl, FindingSeverity, APChannel, ARChannel, 
    PayrollChannel, GLChannel
)
from audit_analysis import AuditAnalyzer
from sample_audit_data import create_sample_company, create_clean_company


__version__ = "DEMO-1.0"
__author__ = "Michael Fillippini"


# =============================================================================
# PAGE CONFIG
# =============================================================================

st.set_page_config(
    page_title="UCF/GUTT Audit - SOX Compliance",
    page_icon="🔍",
    layout="wide",
    initial_sidebar_state="expanded"
)


# =============================================================================
# CUSTOM CSS
# =============================================================================

st.markdown("""
<style>
    /* Demo banner */
    .demo-banner {
        background: linear-gradient(90deg, #dc2626 0%, #b91c1c 100%);
        color: white;
        padding: 12px 20px;
        border-radius: 8px;
        margin-bottom: 20px;
        text-align: center;
        font-weight: 600;
    }
    
    /* Severity badges */
    .severity-critical { 
        background: #dc2626; color: white; 
        padding: 4px 12px; border-radius: 4px; font-weight: bold;
    }
    .severity-high { 
        background: #ea580c; color: white; 
        padding: 4px 12px; border-radius: 4px; font-weight: bold;
    }
    .severity-medium { 
        background: #ca8a04; color: white; 
        padding: 4px 12px; border-radius: 4px;
    }
    .severity-low { 
        background: #16a34a; color: white; 
        padding: 4px 12px; border-radius: 4px;
    }
    .severity-info { 
        background: #2563eb; color: white; 
        padding: 4px 12px; border-radius: 4px;
    }
    
    /* SOX control badges */
    .sox-badge {
        background: #4f46e5;
        color: white;
        padding: 3px 8px;
        border-radius: 3px;
        font-size: 12px;
        margin-right: 5px;
    }
    
    /* Finding card */
    .finding-card {
        background: #1e293b;
        border-left: 4px solid #dc2626;
        padding: 15px;
        margin: 10px 0;
        border-radius: 0 8px 8px 0;
    }
    
    /* Control health */
    .health-good { color: #22c55e; }
    .health-warning { color: #eab308; }
    .health-critical { color: #ef4444; }
    
    /* Metric boxes */
    .metric-box {
        background: #1e293b;
        padding: 20px;
        border-radius: 10px;
        text-align: center;
    }
    
    /* Production comparison */
    .prod-compare {
        background: linear-gradient(135deg, #1e3a5f 0%, #2d4a6f 100%);
        padding: 15px;
        border-radius: 10px;
        border: 2px solid #fbbf24;
        margin-top: 20px;
    }
    
    /* Tables */
    .audit-table {
        width: 100%;
        border-collapse: collapse;
    }
    .audit-table th, .audit-table td {
        padding: 10px;
        border: 1px solid #334155;
        text-align: left;
    }
    .audit-table th {
        background: #1e293b;
    }
</style>
""", unsafe_allow_html=True)


# =============================================================================
# HELPER FUNCTIONS
# =============================================================================

def severity_badge(severity: FindingSeverity) -> str:
    """Generate HTML badge for severity."""
    badges = {
        FindingSeverity.CRITICAL: '<span class="severity-critical">🚨 CRITICAL</span>',
        FindingSeverity.HIGH: '<span class="severity-high">⚠️ HIGH</span>',
        FindingSeverity.MEDIUM: '<span class="severity-medium">⚡ MEDIUM</span>',
        FindingSeverity.LOW: '<span class="severity-low">ℹ️ LOW</span>',
        FindingSeverity.INFO: '<span class="severity-info">📝 INFO</span>',
    }
    return badges.get(severity, '')


def sox_badge(control: SOXControl) -> str:
    """Generate HTML badge for SOX control."""
    if not control:
        return ''
    names = {
        SOXControl.SEGREGATION: "SOD",
        SOXControl.AUTHORIZATION: "AUTH",
        SOXControl.MANAGEMENT_REVIEW: "MGMT",
        SOXControl.RECONCILIATION: "RECON",
        SOXControl.ACCESS_CONTROL: "ACCESS",
        SOXControl.DOCUMENTATION: "DOC",
    }
    return f'<span class="sox-badge">{names.get(control, control.value)}</span>'


def health_color(score: float) -> str:
    """Get color class for health score."""
    if score >= 70:
        return "health-good"
    elif score >= 40:
        return "health-warning"
    return "health-critical"


# =============================================================================
# DATA EXPORT FUNCTIONS
# =============================================================================

def export_universe_to_excel(universe) -> bytes:
    """Export all audit data to Excel workbook."""
    import io
    
    output = io.BytesIO()
    
    with pd.ExcelWriter(output, engine='openpyxl') as writer:
        # Vendors
        if universe.vendors:
            vendors_data = []
            for v in universe.vendors.values():
                vendors_data.append({
                    'ID': v.id,
                    'Name': v.name,
                    'Address': v.address,
                    'Phone': v.phone,
                    'Tax ID': v.tax_id,
                    'Bank Account': v.bank_account,
                    'Is Active': v.is_active,
                    'Approved By': v.approved_by,
                    'Approved Date': str(v.approved_date) if v.approved_date else ''
                })
            pd.DataFrame(vendors_data).to_excel(writer, sheet_name='Vendors', index=False)
        
        # Employees
        if universe.employees:
            emp_data = []
            for e in universe.employees.values():
                emp_data.append({
                    'ID': e.id,
                    'Name': e.name,
                    'Department': e.department,
                    'Title': e.title,
                    'Manager ID': e.manager_id,
                    'Hire Date': str(e.hire_date) if e.hire_date else '',
                    'Termination Date': str(e.termination_date) if e.termination_date else '',
                    'Address': e.address,
                    'Phone': e.phone,
                    'Bank Account': e.bank_account,
                    'Hourly Rate': float(e.hourly_rate) if e.hourly_rate else 0,
                    'Salary': float(e.salary) if e.salary else 0,
                    'Is Management': e.is_management,
                    'Auth Limit': float(e.authorization_limit) if e.authorization_limit else 0
                })
            pd.DataFrame(emp_data).to_excel(writer, sheet_name='Employees', index=False)
        
        # Customers
        if universe.customers:
            cust_data = []
            for c in universe.customers.values():
                cust_data.append({
                    'ID': c.id,
                    'Name': c.name,
                    'Address': c.address,
                    'Phone': c.phone,
                    'Credit Limit': float(c.credit_limit) if c.credit_limit else 0,
                    'Credit Approved By': c.credit_approved_by,
                    'Is Active': c.is_active
                })
            pd.DataFrame(cust_data).to_excel(writer, sheet_name='Customers', index=False)
        
        # AP Transactions
        if universe.ap_transactions:
            ap_data = []
            for t in universe.ap_transactions.values():
                vendor = universe.vendors.get(t.vendor_id)
                ap_data.append({
                    'ID': t.id,
                    'Vendor ID': t.vendor_id,
                    'Vendor Name': vendor.name if vendor else '',
                    'PO Number': t.po_number,
                    'PO Amount': float(t.po_amount),
                    'PO Date': str(t.po_date) if t.po_date else '',
                    'PO Created By': t.po_created_by,
                    'PO Approved By': t.po_approved_by,
                    'Invoice Number': t.invoice_number,
                    'Invoice Amount': float(t.invoice_amount),
                    'Invoice Date': str(t.invoice_date) if t.invoice_date else '',
                    'Invoice Received By': t.invoice_received_by,
                    'Payment Amount': float(t.payment_amount),
                    'Payment Date': str(t.payment_date) if t.payment_date else '',
                    'Payment Approved By': t.payment_approved_by,
                    'Payment Processed By': t.payment_processed_by,
                    'GL Account': t.gl_account,
                    'Description': t.description
                })
            pd.DataFrame(ap_data).to_excel(writer, sheet_name='AP Transactions', index=False)
        
        # AR Transactions
        if universe.ar_transactions:
            ar_data = []
            for t in universe.ar_transactions.values():
                customer = universe.customers.get(t.customer_id)
                ar_data.append({
                    'ID': t.id,
                    'Customer ID': t.customer_id,
                    'Customer Name': customer.name if customer else '',
                    'Invoice Number': t.invoice_number,
                    'Invoice Amount': float(t.invoice_amount),
                    'Invoice Date': str(t.invoice_date) if t.invoice_date else '',
                    'Invoice Created By': t.invoice_created_by,
                    'Due Date': str(t.due_date) if t.due_date else '',
                    'Payment Received': float(t.payment_received),
                    'Payment Date': str(t.payment_date) if t.payment_date else '',
                    'Credit Memo Amount': float(t.credit_memo_amount),
                    'Credit Memo Approved By': t.credit_memo_approved_by,
                    'Write-off Amount': float(t.write_off_amount),
                    'Write-off Approved By': t.write_off_approved_by,
                    'Balance Due': float(t.balance_due()),
                    'Days Outstanding': t.days_outstanding(),
                    'GL Account': t.gl_account,
                    'Description': t.description
                })
            pd.DataFrame(ar_data).to_excel(writer, sheet_name='AR Transactions', index=False)
        
        # Payroll Transactions
        if universe.payroll_transactions:
            pay_data = []
            for t in universe.payroll_transactions.values():
                emp = universe.employees.get(t.employee_id)
                pay_data.append({
                    'ID': t.id,
                    'Employee ID': t.employee_id,
                    'Employee Name': emp.name if emp else '',
                    'Pay Period Start': str(t.pay_period_start) if t.pay_period_start else '',
                    'Pay Period End': str(t.pay_period_end) if t.pay_period_end else '',
                    'Regular Hours': float(t.regular_hours),
                    'Overtime Hours': float(t.overtime_hours),
                    'Hourly Rate': float(t.hourly_rate),
                    'Gross Pay': float(t.gross_pay),
                    'Calculated Gross': float(t.calculated_gross()),
                    'Gross Variance': float(t.gross_variance()),
                    'Deductions': float(t.deductions),
                    'Net Pay': float(t.net_pay),
                    'Has Timesheet': t.has_timesheet,
                    'Timesheet Approved By': t.timesheet_approved_by,
                    'Payroll Processed By': t.payroll_processed_by,
                    'Payment Date': str(t.payment_date) if t.payment_date else '',
                    'GL Account': t.gl_account
                })
            pd.DataFrame(pay_data).to_excel(writer, sheet_name='Payroll', index=False)
        
        # Journal Entries
        if universe.journal_entries:
            je_data = []
            for j in universe.journal_entries.values():
                je_data.append({
                    'ID': j.id,
                    'Entry Date': str(j.entry_date) if j.entry_date else '',
                    'Posting Date': str(j.posting_date) if j.posting_date else '',
                    'Description': j.description,
                    'Total Debits': float(j.total_debits()),
                    'Total Credits': float(j.total_credits()),
                    'Is Balanced': j.is_balanced(),
                    'Is Manual': j.is_manual,
                    'Is Round Amount': j.is_round_amount(),
                    'Created By': j.created_by,
                    'Approved By': j.approved_by,
                    'Source System': j.source_system,
                    'Line Count': len(j.lines)
                })
            pd.DataFrame(je_data).to_excel(writer, sheet_name='Journal Entries', index=False)
            
            # JE Lines detail
            je_lines_data = []
            for j in universe.journal_entries.values():
                for i, line in enumerate(j.lines):
                    je_lines_data.append({
                        'JE ID': j.id,
                        'Line': i + 1,
                        'Account': line.get('account', ''),
                        'Debit': float(line.get('debit', 0)),
                        'Credit': float(line.get('credit', 0))
                    })
            if je_lines_data:
                pd.DataFrame(je_lines_data).to_excel(writer, sheet_name='JE Lines', index=False)
        
        # Findings (if audit has been run)
        if universe.findings:
            findings_data = []
            for f in universe.findings:
                findings_data.append({
                    'ID': f.id,
                    'Domain': f.domain.value,
                    'Severity': f.severity.value,
                    'SOX Control': f.sox_control.value if f.sox_control else '',
                    'Title': f.title,
                    'Description': f.description,
                    'Transaction IDs': ', '.join(f.transaction_ids),
                    'Entity IDs': ', '.join([e for e in f.entity_ids if e]),
                    'Recommendation': f.recommendation
                })
            pd.DataFrame(findings_data).to_excel(writer, sheet_name='Audit Findings', index=False)
    
    output.seek(0)
    return output.getvalue()


def get_findings_df(findings) -> pd.DataFrame:
    """Convert findings to DataFrame."""
    data = []
    for f in findings:
        data.append({
            'ID': f.id,
            'Severity': f.severity.value.upper(),
            'Domain': f.domain.value.replace('_', ' ').title(),
            'SOX Control': f.sox_control.value.replace('_', ' ').title() if f.sox_control else '',
            'Title': f.title,
            'Description': f.description,
            'Transactions': ', '.join(f.transaction_ids),
            'Recommendation': f.recommendation
        })
    return pd.DataFrame(data)


# =============================================================================
# RENDER FUNCTIONS
# =============================================================================

def render_header():
    """Render page header with demo banner."""
    st.markdown("""
    <div class="demo-banner">
        ⚠️ DEMONSTRATION VERSION — Simplified algorithms for concept illustration<br>
        <small>Production system uses proprietary UCF/GUTT tensor analysis with Coq-verified predicates</small>
        <br>
        <a href="mailto:Michael_Fill@ProtonMail.com" style="color: #fbbf24;">
            🔒 Contact for Production License →
        </a>
    </div>
    """, unsafe_allow_html=True)
    
    st.title("🔍 UCF/GUTT Audit Framework")
    st.markdown("**SOX Compliance Analysis** — Relational control testing for AP, AR, Payroll, and GL")


def render_sidebar():
    """Render sidebar with data loading and production comparison."""
    st.sidebar.header("📊 Audit Data")
    
    dataset = st.sidebar.selectbox(
        "Select Dataset",
        ["Acme Corporation (Issues)", "Best Practices Corp (Clean)"]
    )
    
    if st.sidebar.button("📂 Load Dataset", type="primary"):
        if "Issues" in dataset:
            st.session_state.universe = create_sample_company()
        else:
            st.session_state.universe = create_clean_company()
        st.session_state.audit_run = False
        st.rerun()
    
    if 'universe' in st.session_state:
        st.sidebar.success(f"✓ Loaded: {st.session_state.universe.name}")
        stats = st.session_state.universe.stats()
        
        st.sidebar.markdown("**Entity Counts:**")
        col1, col2 = st.sidebar.columns(2)
        with col1:
            st.metric("Vendors", stats['vendors'])
            st.metric("Employees", stats['employees'])
        with col2:
            st.metric("Customers", stats['customers'])
            st.metric("GL Accounts", stats['gl_accounts'])
        
        st.sidebar.markdown("**Transaction Counts:**")
        col1, col2 = st.sidebar.columns(2)
        with col1:
            st.metric("AP Txns", stats['ap_transactions'])
            st.metric("AR Txns", stats['ar_transactions'])
        with col2:
            st.metric("Payroll", stats['payroll_transactions'])
            st.metric("JE's", stats['journal_entries'])
        
        if st.sidebar.button("🔬 Run Full Audit", type="primary"):
            with st.spinner("Running audit analysis..."):
                analyzer = AuditAnalyzer(st.session_state.universe)
                st.session_state.audit_results = analyzer.run_full_audit()
                st.session_state.health_score = analyzer.get_control_health_score()
                st.session_state.audit_run = True
            st.rerun()
        
        # Data Export Section
        st.sidebar.markdown("---")
        st.sidebar.markdown("**📥 Export Data:**")
        
        try:
            excel_data = export_universe_to_excel(st.session_state.universe)
            st.sidebar.download_button(
                label="📊 Download All Data (Excel)",
                data=excel_data,
                file_name=f"audit_data_{st.session_state.universe.name.replace(' ', '_')}.xlsx",
                mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
            )
        except Exception as e:
            st.sidebar.warning(f"Excel export requires openpyxl: pip install openpyxl")
        
        # Export findings separately if audit has run
        if st.session_state.get('audit_run') and st.session_state.universe.findings:
            findings_df = get_findings_df(st.session_state.universe.findings)
            csv_data = findings_df.to_csv(index=False)
            st.sidebar.download_button(
                label="📋 Download Findings (CSV)",
                data=csv_data,
                file_name="audit_findings.csv",
                mime="text/csv"
            )
    
    # Production comparison
    st.sidebar.markdown("---")
    st.sidebar.markdown("""
    <div class="prod-compare">
        <div style="color: #fbbf24; font-weight: bold; margin-bottom: 10px;">
            🔒 PRODUCTION ADDS
        </div>
        <table style="width: 100%; font-size: 11px; color: white;">
            <tr><td>Analysis</td><td style="color: #fca5a5;">Demo: Basic</td></tr>
            <tr><td></td><td style="color: #86efac;">Prod: Tensor-based</td></tr>
            <tr><td>Verification</td><td style="color: #fca5a5;">Demo: None</td></tr>
            <tr><td></td><td style="color: #86efac;">Prod: Coq proofs</td></tr>
            <tr><td>ML Anomaly</td><td style="color: #fca5a5;">Demo: None</td></tr>
            <tr><td></td><td style="color: #86efac;">Prod: Pattern detect</td></tr>
            <tr><td>Temporal</td><td style="color: #fca5a5;">Demo: None</td></tr>
            <tr><td></td><td style="color: #86efac;">Prod: Trend analysis</td></tr>
        </table>
        <div style="margin-top: 12px; text-align: center;">
            <a href="mailto:Michael_Fill@ProtonMail.com" 
               style="color: #fbbf24; text-decoration: none; font-weight: bold;">
            ✉️ License Inquiry →</a>
        </div>
    </div>
    """, unsafe_allow_html=True)


def render_executive_summary(results: Dict, health_score: float):
    """Render executive summary dashboard."""
    st.header("📋 Executive Summary")
    
    summary = results['summary']
    
    # Health score and key metrics
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        # Health gauge
        fig = go.Figure(go.Indicator(
            mode="gauge+number",
            value=health_score,
            domain={'x': [0, 1], 'y': [0, 1]},
            gauge={
                'axis': {'range': [0, 100], 'tickcolor': 'white'},
                'bar': {'color': '#22c55e' if health_score >= 70 else '#ca8a04' if health_score >= 40 else '#dc2626'},
                'bgcolor': '#1e293b',
                'bordercolor': '#334155',
                'steps': [
                    {'range': [0, 40], 'color': 'rgba(220,38,38,0.3)'},
                    {'range': [40, 70], 'color': 'rgba(202,138,4,0.3)'},
                    {'range': [70, 100], 'color': 'rgba(34,197,94,0.3)'}
                ],
            },
            title={'text': "Control Health", 'font': {'color': 'white'}}
        ))
        fig.update_layout(
            height=200,
            paper_bgcolor='rgba(0,0,0,0)',
            font={'color': 'white'}
        )
        st.plotly_chart(fig, use_container_width=True)
    
    with col2:
        st.metric("🚨 Critical Findings", summary['critical_count'])
    
    with col3:
        st.metric("⚠️ High Findings", summary['high_count'])
    
    with col4:
        st.metric("👥 Related Party Issues", summary['related_party_count'])
    
    st.markdown("---")
    
    # Charts
    render_findings_chart(results)


def render_findings_by_domain(results: Dict, domain: str, title: str):
    """Render findings for a specific domain."""
    findings = results.get(f'{domain}_findings', [])
    
    st.header(f"{title} ({len(findings)} findings)")
    
    if not findings:
        st.success("✅ No issues found!")
        return
    
    # Group by severity
    critical = [f for f in findings if f.severity == FindingSeverity.CRITICAL]
    high = [f for f in findings if f.severity == FindingSeverity.HIGH]
    medium = [f for f in findings if f.severity == FindingSeverity.MEDIUM]
    low_info = [f for f in findings if f.severity in [FindingSeverity.LOW, FindingSeverity.INFO]]
    
    if critical:
        st.error(f"🚨 {len(critical)} Critical Issues")
        for f in critical:
            with st.expander(f"**{f.title}**"):
                render_finding_detail(f)
    
    if high:
        st.warning(f"⚠️ {len(high)} High Issues")
        for f in high:
            with st.expander(f"**{f.title}**"):
                render_finding_detail(f)
    
    if medium:
        st.info(f"⚡ {len(medium)} Medium Issues")
        for f in medium:
            with st.expander(f"{f.title}"):
                render_finding_detail(f)
    
    if low_info:
        with st.expander(f"ℹ️ {len(low_info)} Low/Info Issues"):
            for f in low_info:
                st.markdown(f"**{f.title}**: {f.description}")


def render_finding_detail(finding: AuditFinding):
    """Render detailed finding information."""
    col1, col2 = st.columns([3, 1])
    
    with col1:
        st.markdown(f"**Description:** {finding.description}")
        st.markdown(f"**Recommendation:** {finding.recommendation}")
        
        if finding.transaction_ids:
            st.markdown(f"**Transaction(s):** {', '.join(finding.transaction_ids)}")
        
        if finding.entity_ids:
            st.markdown(f"**Entity(ies):** {', '.join([e for e in finding.entity_ids if e])}")
    
    with col2:
        st.markdown(severity_badge(finding.severity), unsafe_allow_html=True)
        if finding.sox_control:
            st.markdown(f"**SOX Control:** {finding.sox_control.value.replace('_', ' ').title()}")
        
        if finding.channel_violations:
            st.markdown("**Channels Violated:**")
            for ch, weight in finding.channel_violations.items():
                st.markdown(f"- {ch}: {weight:.1f}")


def render_ap_data(universe):
    """Render AP transactions data view."""
    st.header("📊 AP Transaction Data")
    st.markdown("View source AP transactions. **Red indicators** show potential issues to investigate.")
    
    if not universe.ap_transactions:
        st.info("No AP transactions")
        return
    
    data = []
    for t in universe.ap_transactions.values():
        vendor = universe.vendors.get(t.vendor_id)
        match_ok, _ = t.three_way_match()
        
        # Check for related findings
        has_finding = any(t.id in f.transaction_ids for f in universe.findings)
        
        data.append({
            '⚠️': '🔴' if has_finding else '',
            'ID': t.id,
            'Vendor': vendor.name if vendor else t.vendor_id,
            'Vendor Active': '✓' if vendor and vendor.is_active else '❌',
            'PO #': t.po_number or '❌ MISSING',
            'PO Date': str(t.po_date) if t.po_date else '—',
            'PO Amount': float(t.po_amount),
            'PO Approved By': t.po_approved_by or '❌',
            'Invoice #': t.invoice_number or '❌ MISSING',
            'Invoice Date': str(t.invoice_date) if t.invoice_date else '—',
            'Invoice Amount': float(t.invoice_amount),
            'Payment Amount': float(t.payment_amount),
            'Payment Date': str(t.payment_date) if t.payment_date else '—',
            '3-Way Match': '✓' if match_ok else '❌ MISMATCH',
            'Payment Approved': t.payment_approved_by or '❌',
            'Processed By': t.payment_processed_by or '—',
            'GL Account': t.gl_account,
            'Description': t.description
        })
    
    df = pd.DataFrame(data)
    
    st.dataframe(
        df,
        use_container_width=True,
        height=500,
        column_config={
            "PO Amount": st.column_config.NumberColumn(format="$%.2f"),
            "Invoice Amount": st.column_config.NumberColumn(format="$%.2f"),
            "Payment Amount": st.column_config.NumberColumn(format="$%.2f"),
        }
    )
    
    st.markdown("**Legend:** 🔴 = Has audit finding | ❌ = Missing/Issue | ✓ = OK")
    
    # Summary stats
    col1, col2, col3 = st.columns(3)
    with col1:
        st.metric("Total Transactions", len(data))
    with col2:
        st.metric("Total Payments", f"${sum(d['Payment Amount'] for d in data):,.2f}")
    with col3:
        issues = sum(1 for d in data if d['⚠️'] == '🔴')
        st.metric("With Findings", issues)


def render_ar_data(universe):
    """Render AR transactions data view."""
    st.header("📊 AR Transaction Data")
    st.markdown("View source AR transactions. **Red indicators** show potential issues to investigate.")
    
    if not universe.ar_transactions:
        st.info("No AR transactions")
        return
    
    data = []
    for t in universe.ar_transactions.values():
        customer = universe.customers.get(t.customer_id)
        has_finding = any(t.id in f.transaction_ids for f in universe.findings)
        days_out = t.days_outstanding()
        
        data.append({
            '⚠️': '🔴' if has_finding else '',
            'ID': t.id,
            'Customer': customer.name if customer else t.customer_id,
            'Invoice #': t.invoice_number,
            'Invoice Date': str(t.invoice_date) if t.invoice_date else '—',
            'Due Date': str(t.due_date) if t.due_date else '—',
            'Invoice Amount': float(t.invoice_amount),
            'Payment Received': float(t.payment_received),
            'Payment Date': str(t.payment_date) if t.payment_date else '—',
            'Credit Memo': float(t.credit_memo_amount),
            'CM Approved': t.credit_memo_approved_by or '—',
            'Write-off': float(t.write_off_amount),
            'W/O Approved': t.write_off_approved_by or '—',
            'Balance Due': float(t.balance_due()),
            'Days Outstanding': days_out,
            'Aging': '🔴 >90' if days_out > 90 else '🟡 >60' if days_out > 60 else '🟢 Current',
            'GL Account': t.gl_account
        })
    
    df = pd.DataFrame(data)
    
    st.dataframe(
        df,
        use_container_width=True,
        height=500,
        column_config={
            "Invoice Amount": st.column_config.NumberColumn(format="$%.2f"),
            "Payment Received": st.column_config.NumberColumn(format="$%.2f"),
            "Credit Memo": st.column_config.NumberColumn(format="$%.2f"),
            "Write-off": st.column_config.NumberColumn(format="$%.2f"),
            "Balance Due": st.column_config.NumberColumn(format="$%.2f"),
        }
    )
    
    st.markdown("**Legend:** 🔴 = Has finding / >90 days | 🟡 = >60 days | 🟢 = Current | ✓ = OK")
    
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("Total Invoiced", f"${sum(d['Invoice Amount'] for d in data):,.2f}")
    with col2:
        st.metric("Total Received", f"${sum(d['Payment Received'] for d in data):,.2f}")
    with col3:
        st.metric("Total Outstanding", f"${sum(d['Balance Due'] for d in data):,.2f}")
    with col4:
        aged = sum(1 for d in data if d['Days Outstanding'] > 90)
        st.metric("Over 90 Days", aged)


def render_payroll_data(universe):
    """Render Payroll transactions data view."""
    st.header("📊 Payroll Transaction Data")
    st.markdown("View source payroll transactions. **Red indicators** show potential issues to investigate.")
    
    if not universe.payroll_transactions:
        st.info("No payroll transactions")
        return
    
    data = []
    for t in universe.payroll_transactions.values():
        emp = universe.employees.get(t.employee_id)
        emp_exists = emp is not None
        emp_active = emp.is_active(t.pay_period_end) if emp else False
        has_finding = any(t.id in f.transaction_ids for f in universe.findings)
        variance = float(t.gross_variance())
        
        data.append({
            '⚠️': '🔴' if has_finding else '',
            'ID': t.id,
            'Employee': emp.name if emp else f'❌ UNKNOWN ({t.employee_id})',
            'Emp Exists': '✓' if emp_exists else '❌ GHOST',
            'Emp Active': '✓' if emp_active else '❌ TERM',
            'Pay Period': f"{t.pay_period_start} to {t.pay_period_end}",
            'Regular Hrs': float(t.regular_hours),
            'OT Hours': float(t.overtime_hours),
            'Hourly Rate': float(t.hourly_rate),
            'Gross Pay': float(t.gross_pay),
            'Calculated': float(t.calculated_gross()),
            'Variance': variance,
            'Variance OK': '✓' if abs(variance) < 0.01 else '❌',
            'Deductions': float(t.deductions),
            'Net Pay': float(t.net_pay),
            'Timesheet': '✓' if t.has_timesheet else '❌ MISSING',
            'TS Approved': t.timesheet_approved_by or '❌',
            'Processed By': t.payroll_processed_by or '—',
            'GL Account': t.gl_account
        })
    
    df = pd.DataFrame(data)
    
    st.dataframe(
        df,
        use_container_width=True,
        height=500,
        column_config={
            "Hourly Rate": st.column_config.NumberColumn(format="$%.2f"),
            "Gross Pay": st.column_config.NumberColumn(format="$%.2f"),
            "Calculated": st.column_config.NumberColumn(format="$%.2f"),
            "Variance": st.column_config.NumberColumn(format="$%.2f"),
            "Deductions": st.column_config.NumberColumn(format="$%.2f"),
            "Net Pay": st.column_config.NumberColumn(format="$%.2f"),
        }
    )
    
    st.markdown("**Legend:** 🔴 = Has finding | ❌ = Missing/Issue | ✓ = OK")
    
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("Total Gross", f"${sum(d['Gross Pay'] for d in data):,.2f}")
    with col2:
        st.metric("Total Net", f"${sum(d['Net Pay'] for d in data):,.2f}")
    with col3:
        no_ts = sum(1 for d in data if d['Timesheet'] == '❌ MISSING')
        st.metric("Missing Timesheets", no_ts)
    with col4:
        issues = sum(1 for d in data if d['⚠️'] == '🔴')
        st.metric("With Findings", issues)


def render_gl_data(universe):
    """Render GL/Journal Entry data view."""
    st.header("📊 Journal Entry Data")
    st.markdown("View source journal entries. **Red indicators** show potential issues to investigate.")
    
    if not universe.journal_entries:
        st.info("No journal entries")
        return
    
    # Summary view
    st.subheader("Journal Entry Summary")
    
    data = []
    for j in universe.journal_entries.values():
        has_finding = any(j.id in f.transaction_ids for f in universe.findings)
        
        data.append({
            '⚠️': '🔴' if has_finding else '',
            'ID': j.id,
            'Entry Date': str(j.entry_date) if j.entry_date else '—',
            'Posting Date': str(j.posting_date) if j.posting_date else '—',
            'Description': j.description,
            'Total Debits': float(j.total_debits()),
            'Total Credits': float(j.total_credits()),
            'Balanced': '✓' if j.is_balanced() else '❌ UNBALANCED',
            'Manual Entry': '⚠️ YES' if j.is_manual else 'No',
            'Round Amount': '⚠️ YES' if j.is_round_amount() else 'No',
            'Created By': j.created_by,
            'Approved By': j.approved_by or '❌ NONE',
            'Self-Approved': '⚠️ YES' if j.created_by == j.approved_by and j.approved_by else '—',
            'Source System': j.source_system or '—',
            'Line Count': len(j.lines)
        })
    
    df = pd.DataFrame(data)
    
    st.dataframe(
        df,
        use_container_width=True,
        height=350,
        column_config={
            "Total Debits": st.column_config.NumberColumn(format="$%.2f"),
            "Total Credits": st.column_config.NumberColumn(format="$%.2f"),
        }
    )
    
    # Line detail
    st.subheader("Journal Entry Line Detail")
    
    je_select = st.selectbox(
        "Select Journal Entry",
        list(universe.journal_entries.keys()),
        format_func=lambda x: f"{x}: {universe.journal_entries[x].description[:50]}"
    )
    
    if je_select:
        je = universe.journal_entries[je_select]
        lines_data = []
        for i, line in enumerate(je.lines):
            lines_data.append({
                'Line': i + 1,
                'Account': line.get('account', ''),
                'Description': line.get('description', ''),
                'Debit': float(line.get('debit', 0)),
                'Credit': float(line.get('credit', 0))
            })
        
        lines_df = pd.DataFrame(lines_data)
        st.dataframe(
            lines_df,
            use_container_width=True,
            column_config={
                "Debit": st.column_config.NumberColumn(format="$%.2f"),
                "Credit": st.column_config.NumberColumn(format="$%.2f"),
            }
        )
    
    st.markdown("**Legend:** 🔴 = Has finding | ⚠️ = Warning indicator | ❌ = Issue | ✓ = OK")


def render_master_data(universe):
    """Render master data (Vendors, Employees, Customers)."""
    st.header("📊 Master Data")
    
    master_tab = st.selectbox(
        "Select Master Data Type",
        ["Vendors", "Employees", "Customers"]
    )
    
    if master_tab == "Vendors":
        st.subheader("🏪 Vendor Master")
        if universe.vendors:
            data = []
            for v in universe.vendors.values():
                # Check for related party
                is_related = any('related party' in f.title.lower() and v.id in f.entity_ids 
                               for f in universe.findings)
                data.append({
                    '⚠️': '🔴' if is_related else '',
                    'ID': v.id,
                    'Name': v.name,
                    'Address': v.address,
                    'Phone': v.phone,
                    'Tax ID': v.tax_id,
                    'Bank Account': v.bank_account[-4:] + '****' if v.bank_account else '—',
                    'Active': '✓' if v.is_active else '❌ Inactive',
                    'Approved By': v.approved_by or '❌ NOT APPROVED',
                    'Approved Date': str(v.approved_date) if v.approved_date else '—'
                })
            df = pd.DataFrame(data)
            st.dataframe(df, use_container_width=True, height=400)
        else:
            st.info("No vendors")
    
    elif master_tab == "Employees":
        st.subheader("👤 Employee Master")
        if universe.employees:
            data = []
            for e in universe.employees.values():
                # Check for related party
                is_related = any('related party' in f.title.lower() and e.id in f.entity_ids 
                               for f in universe.findings)
                data.append({
                    '⚠️': '🔴' if is_related else '',
                    'ID': e.id,
                    'Name': e.name,
                    'Department': e.department,
                    'Title': e.title,
                    'Manager': e.manager_id or '—',
                    'Hire Date': str(e.hire_date) if e.hire_date else '—',
                    'Term Date': str(e.termination_date) if e.termination_date else '—',
                    'Active': '✓' if e.is_active() else '❌',
                    'Management': '⭐' if e.is_management else '—',
                    'Auth Limit': f"${float(e.authorization_limit):,.0f}" if e.authorization_limit else '—',
                    'Address': e.address,
                    'Phone': e.phone,
                    'Bank (last 4)': e.bank_account[-4:] if e.bank_account else '—'
                })
            df = pd.DataFrame(data)
            st.dataframe(df, use_container_width=True, height=400)
        else:
            st.info("No employees")
    
    elif master_tab == "Customers":
        st.subheader("👥 Customer Master")
        if universe.customers:
            data = []
            for c in universe.customers.values():
                total_out = sum(float(t.balance_due()) for t in universe.ar_transactions.values() 
                               if t.customer_id == c.id)
                over_limit = total_out > float(c.credit_limit) if c.credit_limit else False
                data.append({
                    '⚠️': '🔴' if over_limit else '',
                    'ID': c.id,
                    'Name': c.name,
                    'Address': c.address,
                    'Phone': c.phone,
                    'Credit Limit': float(c.credit_limit) if c.credit_limit else 0,
                    'Outstanding': total_out,
                    'Over Limit': '⚠️ YES' if over_limit else '—',
                    'Active': '✓' if c.is_active else '❌',
                    'Credit Approved By': c.credit_approved_by or '—'
                })
            df = pd.DataFrame(data)
            st.dataframe(
                df,
                use_container_width=True,
                height=400,
                column_config={
                    "Credit Limit": st.column_config.NumberColumn(format="$%.0f"),
                    "Outstanding": st.column_config.NumberColumn(format="$%.2f"),
                }
            )
        else:
            st.info("No customers")
    
    st.markdown("**Legend:** 🔴 = Related party / Over limit | ❌ = Issue | ✓ = OK | ⭐ = Management")


def render_related_parties(results: Dict):
    """Render related party findings."""
    findings = results.get('related_party_findings', [])
    
    st.header(f"👥 Related Party Analysis ({len(findings)} issues)")
    
    st.markdown("""
    <div style="background: #1e293b; padding: 15px; border-radius: 8px; margin-bottom: 20px; color: #e2e8f0;">
        <strong style="color: #f1f5f9;">What is Related Party Detection?</strong><br>
        Identifying relationships between employees and vendors/customers that could indicate:
        <ul style="color: #cbd5e1; margin-top: 10px;">
            <li>Conflict of interest</li>
            <li>Shell company fraud</li>
            <li>Kickback schemes</li>
            <li>Undisclosed relationships</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)
    
    if not findings:
        st.success("✅ No related party issues detected!")
        return
    
    for f in findings:
        severity_class = "error" if f.severity == FindingSeverity.CRITICAL else "warning"
        if severity_class == "error":
            st.error(f"🚨 **{f.title}**: {f.description}")
        else:
            st.warning(f"⚠️ **{f.title}**: {f.description}")
        st.markdown(f"*Recommendation:* {f.recommendation}")
        st.markdown("---")


def render_channel_heatmap(domain: TransactionDomain):
    """Render channel compliance heatmap with HTML table for reliable text display."""
    if 'universe' not in st.session_state:
        return
    
    universe = st.session_state.universe
    tensor = universe.get_tensor(domain)
    
    # Get channel enum
    if domain == TransactionDomain.AP:
        channels = list(APChannel)
        transactions = universe.ap_transactions
        get_target = lambda txn: txn.vendor_id
        get_name = lambda txn: universe.vendors.get(txn.vendor_id, None)
        domain_label = "AP"
    elif domain == TransactionDomain.AR:
        channels = list(ARChannel)
        transactions = universe.ar_transactions
        get_target = lambda txn: txn.customer_id
        get_name = lambda txn: universe.customers.get(txn.customer_id, None)
        domain_label = "AR"
    elif domain == TransactionDomain.PAYROLL:
        channels = list(PayrollChannel)
        transactions = universe.payroll_transactions
        get_target = lambda txn: txn.employee_id
        get_name = lambda txn: universe.employees.get(txn.employee_id, None)
        domain_label = "Payroll"
    else:
        return
    
    if not transactions:
        st.info("No transactions to display")
        return
    
    # Channel descriptions
    channel_desc = {
        'documentation': 'Supporting documents exist and match requirements',
        'authorization': 'Proper approval chain was followed',
        'timing': 'Correct chronological sequence of events',
        'amount': 'Values reconcile across documents (3-way match)',
        'counterparty': 'Vendor/entity is legitimate and approved',
        'customer': 'Customer credit status is acceptable',
        'employee': 'Employee exists and is active',
        'segregation': 'Duties are properly separated (different people)',
        'balance': 'Debits equal credits'
    }
    
    # Build HTML table
    txn_list = list(transactions.items())
    
    html = '''
    <style>
        .matrix-container {
            overflow-x: auto;
            margin: 10px 0;
        }
        .matrix-table {
            border-collapse: collapse;
            width: 100%;
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
        }
        .matrix-table th {
            background: #1e293b;
            color: #e2e8f0;
            padding: 12px 8px;
            border: 1px solid #334155;
            font-weight: 600;
            font-size: 12px;
            text-align: center;
            position: sticky;
            top: 0;
        }
        .matrix-table td {
            padding: 10px 8px;
            border: 1px solid #334155;
            text-align: center;
            font-size: 18px;
            font-weight: bold;
        }
        .matrix-table tr:hover {
            background: rgba(255,255,255,0.05);
        }
        .cell-pass {
            background: #166534;
            color: white;
        }
        .cell-fail {
            background: #991b1b;
            color: white;
        }
        .cell-na {
            background: #374151;
            color: #9ca3af;
        }
        .cell-txn {
            background: #1e293b;
            color: #f1f5f9;
            text-align: left;
            font-size: 13px;
            font-weight: 600;
            max-width: 120px;
            overflow: hidden;
            text-overflow: ellipsis;
            white-space: nowrap;
        }
        .cell-entity {
            background: #1e293b;
            color: #94a3b8;
            text-align: left;
            font-size: 12px;
            max-width: 150px;
            overflow: hidden;
            text-overflow: ellipsis;
            white-space: nowrap;
        }
        .status-pass {
            background: #166534;
            color: white;
            font-weight: bold;
        }
        .status-fail {
            background: #991b1b;
            color: white;
            font-weight: bold;
        }
        .matrix-table td[title] {
            cursor: help;
        }
    </style>
    <div class="matrix-container">
    <table class="matrix-table">
    <thead>
    <tr>
        <th>Transaction</th>
        <th>Entity</th>
    '''
    
    # Add channel headers
    for ch in channels:
        html += f'<th>{ch.value.title()}</th>'
    html += '<th>Status</th></tr></thead><tbody>'
    
    # Track stats
    total_pass = 0
    total_fail = 0
    total_na = 0
    
    # Add data rows
    for txn_id, txn in txn_list:
        target = get_target(txn)
        entity = get_name(txn)
        entity_name = entity.name if entity else target
        
        html += '<tr>'
        html += f'<td class="cell-txn" title="{txn_id}">{txn_id}</td>'
        html += f'<td class="cell-entity" title="{entity_name}">{entity_name[:20]}{"..." if len(entity_name) > 20 else ""}</td>'
        
        row_fail = False
        for ch in channels:
            weight = tensor.get_weight(ch.value, txn_id, target)
            desc = channel_desc.get(ch.value, ch.value)
            
            tooltip = f"{ch.value.title()}: {desc} | Weight: {weight:.1f}"
            
            if weight > 0:
                html += f'<td class="cell-pass" title="{tooltip}">✓</td>'
                total_pass += 1
            elif weight < 0:
                html += f'<td class="cell-fail" title="{tooltip}">✗</td>'
                total_fail += 1
                row_fail = True
            else:
                html += f'<td class="cell-na" title="{tooltip}">—</td>'
                total_na += 1
        
        # Row status
        if row_fail:
            html += '<td class="status-fail">FAIL</td>'
        else:
            html += '<td class="status-pass">PASS</td>'
        
        html += '</tr>'
    
    html += '</tbody></table></div>'
    
    # Calculate height based on rows
    table_height = min(600, 80 + len(txn_list) * 45)
    
    # Render HTML
    components.html(html, height=table_height, scrolling=True)
    
    st.markdown("**Hover over cells** for control details | ✓ PASS | — N/A | ✗ FAIL")
    
    # Summary stats
    total_tests = total_pass + total_fail + total_na
    
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("Total Tests", total_tests)
    with col2:
        st.metric("Passed", total_pass, delta=f"{total_pass/total_tests*100:.0f}%" if total_tests > 0 else "0%")
    with col3:
        st.metric("Failed", total_fail, delta=f"-{total_fail}" if total_fail > 0 else None, delta_color="inverse")
    with col4:
        st.metric("N/A", total_na)
    
    # Channel reference guide
    with st.expander("📖 Control Channel Reference", expanded=False):
        for ch in channels:
            desc = channel_desc.get(ch.value, ch.value)
            st.markdown(f"**{ch.value.title()}**: {desc}")
    
    # Detailed transaction view
    st.markdown("---")
    st.subheader("🔍 Transaction Detail View")
    
    txn_ids = [t[0] for t in txn_list]
    txn_select = st.selectbox(
        "Select a transaction to view full control details:",
        txn_ids,
        key=f"matrix_txn_select_{domain_label}"
    )
    
    if txn_select:
        txn = transactions[txn_select]
        target = get_target(txn)
        entity = get_name(txn)
        entity_name = entity.name if entity else target
        
        st.markdown(f"**Transaction:** `{txn_select}` → **Entity:** `{entity_name}`")
        
        # Show each channel as a card
        cols = st.columns(3)
        for i, ch in enumerate(channels):
            weight = tensor.get_weight(ch.value, txn_select, target)
            desc = channel_desc.get(ch.value, ch.value)
            
            with cols[i % 3]:
                if weight > 0:
                    st.success(f"**{ch.value.title()}**\n\n✓ PASS (weight: +{weight:.1f})\n\n{desc}")
                elif weight < 0:
                    st.error(f"**{ch.value.title()}**\n\n✗ FAIL (weight: {weight:.1f})\n\n{desc}")
                else:
                    st.info(f"**{ch.value.title()}**\n\n— N/A (not tested)\n\n{desc}")
        
        # Show related findings
        related_findings = [f for f in universe.findings if txn_select in f.transaction_ids]
        if related_findings:
            st.markdown("---")
            st.markdown(f"**⚠️ Related Audit Findings ({len(related_findings)}):**")
            for f in related_findings:
                severity_color = {
                    'critical': '🔴', 'high': '🟠', 'medium': '🟡', 'low': '🟢', 'informational': '🔵'
                }.get(f.severity.value, '⚪')
                st.markdown(f"{severity_color} **{f.severity.value.upper()}**: {f.title}")
                st.caption(f.description)


def render_findings_chart(results: Dict):
    """Render findings distribution charts."""
    summary = results['summary']
    
    col1, col2 = st.columns(2)
    
    with col1:
        # Severity pie chart
        severity_data = {
            'Severity': ['Critical', 'High', 'Medium', 'Low', 'Info'],
            'Count': [
                summary['by_severity']['critical'],
                summary['by_severity']['high'],
                summary['by_severity']['medium'],
                summary['by_severity']['low'],
                summary['by_severity']['informational']
            ],
            'Color': ['#dc2626', '#ea580c', '#ca8a04', '#22c55e', '#3b82f6']
        }
        df = pd.DataFrame(severity_data)
        df = df[df['Count'] > 0]
        
        if not df.empty:
            fig = px.pie(df, values='Count', names='Severity',
                        color='Severity',
                        color_discrete_map={
                            'Critical': '#dc2626',
                            'High': '#ea580c',
                            'Medium': '#ca8a04',
                            'Low': '#22c55e',
                            'Info': '#3b82f6'
                        },
                        title="Findings by Severity")
            fig.update_layout(
                paper_bgcolor='rgba(0,0,0,0)',
                plot_bgcolor='rgba(0,0,0,0)',
                font=dict(color='white')
            )
            st.plotly_chart(fig, use_container_width=True)
    
    with col2:
        # Domain bar chart
        domain_data = {
            'Domain': ['AP', 'AR', 'Payroll', 'GL'],
            'Findings': [
                summary['by_domain']['accounts_payable'],
                summary['by_domain']['accounts_receivable'],
                summary['by_domain']['payroll'],
                summary['by_domain']['general_ledger']
            ]
        }
        df = pd.DataFrame(domain_data)
        
        fig = px.bar(df, x='Domain', y='Findings',
                    color='Findings',
                    color_continuous_scale=['#22c55e', '#ca8a04', '#dc2626'],
                    title="Findings by Domain")
        fig.update_layout(
            paper_bgcolor='rgba(0,0,0,0)',
            plot_bgcolor='rgba(0,0,0,0)',
            font=dict(color='white'),
            showlegend=False
        )
        st.plotly_chart(fig, use_container_width=True)


def render_transaction_network():
    """Render interactive transaction network visualization using pyvis."""
    if 'universe' not in st.session_state:
        return
    
    if not PYVIS_AVAILABLE:
        st.warning("⚠️ Install pyvis for interactive network: `pip install pyvis`")
        st.info("Showing static network instead...")
        render_transaction_network_static()
        return
    
    universe = st.session_state.universe
    
    domain = st.selectbox(
        "Select Domain for Network",
        ["AP - Vendor Payments", "AR - Customer Invoices", "Payroll - Employee Payments"],
        key="network_domain"
    )
    
    # Create pyvis network - EXTRA LARGE SIZE
    net = Network(height="900px", width="100%", bgcolor="#0f172a", font_color="white")
    net.barnes_hut(gravity=-6000, central_gravity=0.2, spring_length=350)
    
    # Set options for much larger fonts
    net.set_options('''
    {
        "nodes": {
            "font": {
                "size": 24,
                "color": "white",
                "face": "arial"
            },
            "scaling": {
                "min": 30,
                "max": 60
            }
        },
        "edges": {
            "font": {
                "size": 18,
                "color": "white"
            },
            "width": 2
        },
        "physics": {
            "barnesHut": {
                "gravitationalConstant": -6000,
                "springLength": 350,
                "springConstant": 0.01
            }
        }
    }
    ''')
    
    # Add company node (central) - EXTRA LARGE
    net.add_node("COMPANY", label="🏢 COMPANY", color="#3b82f6", size=70, 
                 title="COMPANY\n(Central Entity)")
    
    if "AP" in domain:
        # Build AP network: Company -> Vendors
        vendor_totals = {}
        vendor_issues = {}
        
        for txn in universe.ap_transactions.values():
            vendor = universe.vendors.get(txn.vendor_id)
            vendor_name = vendor.name if vendor else txn.vendor_id
            
            # Accumulate totals
            if vendor_name not in vendor_totals:
                vendor_totals[vendor_name] = 0
                vendor_issues[vendor_name] = []
            vendor_totals[vendor_name] += float(txn.payment_amount)
            
            # Check for issues
            tensor = universe.ap_tensor
            for ch in APChannel:
                w = tensor.get_weight(ch.value, txn.id, txn.vendor_id)
                if w < 0:
                    vendor_issues[vendor_name].append(f"{txn.id}: {ch.value}")
        
        for vendor_name, total in vendor_totals.items():
            issues = vendor_issues[vendor_name]
            has_issue = len(issues) > 0
            
            # Build tooltip (plain text)
            tooltip = f"VENDOR: {vendor_name}\n"
            tooltip += f"Total Payments: ${total:,.2f}\n"
            if has_issue:
                tooltip += f"\n⚠️ {len(issues)} Control Issues:\n"
                for issue in issues[:5]:
                    tooltip += f"  • {issue}\n"
                if len(issues) > 5:
                    tooltip += f"  • ...and {len(issues)-5} more"
            else:
                tooltip += "\n✓ All controls passed"
            
            color = "#dc2626" if has_issue else "#22c55e"
            # EXTRA LARGE nodes
            net.add_node(vendor_name, label=f"🏪 {vendor_name}", color=color,
                        size=45 + min(total/5000, 30), title=tooltip)
            
            edge_color = "#dc2626" if has_issue else "#22c55e"
            net.add_edge("COMPANY", vendor_name, color=edge_color, 
                        title=f"${total:,.2f}", value=total/10000)
    
    elif "AR" in domain:
        customer_totals = {}
        customer_issues = {}
        
        for txn in universe.ar_transactions.values():
            customer = universe.customers.get(txn.customer_id)
            customer_name = customer.name if customer else txn.customer_id
            
            if customer_name not in customer_totals:
                customer_totals[customer_name] = 0
                customer_issues[customer_name] = []
            customer_totals[customer_name] += float(txn.invoice_amount)
            
            # Check findings
            for f in universe.findings:
                if txn.id in f.transaction_ids:
                    customer_issues[customer_name].append(f"{txn.id}: {f.title}")
        
        for customer_name, total in customer_totals.items():
            issues = customer_issues[customer_name]
            has_issue = len(issues) > 0
            
            # Plain text tooltip
            tooltip = f"CUSTOMER: {customer_name}\n"
            tooltip += f"Total Invoiced: ${total:,.2f}\n"
            if has_issue:
                tooltip += f"\n⚠️ {len(issues)} Issues:\n"
                for issue in issues[:5]:
                    tooltip += f"  • {issue}\n"
            else:
                tooltip += "\n✓ Clean"
            
            color = "#dc2626" if has_issue else "#22c55e"
            # EXTRA LARGE nodes
            net.add_node(customer_name, label=f"👤 {customer_name}", color=color,
                        size=45 + min(total/10000, 30), title=tooltip)
            
            edge_color = "#dc2626" if has_issue else "#22c55e"
            net.add_edge(customer_name, "COMPANY", color=edge_color,
                        title=f"${total:,.2f}", value=total/10000)
    
    else:  # Payroll
        emp_totals = {}
        emp_issues = {}
        
        for txn in universe.payroll_transactions.values():
            emp = universe.employees.get(txn.employee_id)
            emp_name = emp.name if emp else txn.employee_id
            
            if emp_name not in emp_totals:
                emp_totals[emp_name] = 0
                emp_issues[emp_name] = []
            emp_totals[emp_name] += float(txn.net_pay)
            
            for f in universe.findings:
                if txn.id in f.transaction_ids:
                    emp_issues[emp_name].append(f"{txn.id}: {f.title}")
        
        for emp_name, total in emp_totals.items():
            issues = emp_issues[emp_name]
            has_issue = len(issues) > 0
            
            # Plain text tooltip
            tooltip = f"EMPLOYEE: {emp_name}\n"
            tooltip += f"Total Net Pay: ${total:,.2f}\n"
            if has_issue:
                tooltip += f"\n⚠️ {len(issues)} Issues:\n"
                for issue in issues[:5]:
                    tooltip += f"  • {issue}\n"
            else:
                tooltip += "\n✓ Clean"
            
            color = "#dc2626" if has_issue else "#22c55e"
            # EXTRA LARGE nodes
            net.add_node(emp_name, label=f"👷 {emp_name}", color=color,
                        size=45, title=tooltip)
            
            edge_color = "#dc2626" if has_issue else "#22c55e"
            net.add_edge("COMPANY", emp_name, color=edge_color,
                        title=f"${total:,.2f}", value=total/1000)
    
    # Generate HTML and display - LARGER HEIGHT
    try:
        # Use temp file approach
        with tempfile.NamedTemporaryFile(delete=False, suffix='.html', mode='w') as f:
            net.save_graph(f.name)
            f.seek(0)
        
        with open(f.name, 'r') as f:
            html_content = f.read()
        
        os.unlink(f.name)
        
        components.html(html_content, height=920, scrolling=False)
        
    except Exception as e:
        st.error(f"Network visualization error: {e}")
        st.info("Falling back to static view")
    
    st.caption("🟢 Clean | 🔴 Has findings | 🔵 Company — **Hover over nodes for details, drag to rearrange**")


def render_transaction_network_static():
    """Static fallback network visualization using Plotly (when pyvis not available)."""
    if 'universe' not in st.session_state:
        return
    
    universe = st.session_state.universe
    
    domain = st.selectbox(
        "Select Domain for Network",
        ["AP - Vendor Payments", "AR - Customer Invoices", "Payroll - Employee Payments"],
        key="network_domain_static"
    )
    
    G = nx.DiGraph()
    
    if "AP" in domain:
        for txn in universe.ap_transactions.values():
            vendor = universe.vendors.get(txn.vendor_id)
            vendor_name = vendor.name if vendor else txn.vendor_id
            has_issue = any(txn.id in f.transaction_ids for f in universe.findings)
            
            G.add_node("COMPANY", node_type="company", color="#3b82f6")
            G.add_node(vendor_name, node_type="vendor", 
                      color="#dc2626" if has_issue else "#22c55e",
                      has_issue=has_issue)
            G.add_edge("COMPANY", vendor_name, 
                      amount=float(txn.payment_amount),
                      has_issue=has_issue)
    
    elif "AR" in domain:
        for txn in universe.ar_transactions.values():
            customer = universe.customers.get(txn.customer_id)
            customer_name = customer.name if customer else txn.customer_id
            has_issue = any(txn.id in f.transaction_ids for f in universe.findings)
            
            G.add_node(customer_name, node_type="customer",
                      color="#dc2626" if has_issue else "#22c55e")
            G.add_node("COMPANY", node_type="company", color="#3b82f6")
            G.add_edge(customer_name, "COMPANY",
                      amount=float(txn.invoice_amount),
                      has_issue=has_issue)
    
    else:  # Payroll
        for txn in universe.payroll_transactions.values():
            emp = universe.employees.get(txn.employee_id)
            emp_name = emp.name if emp else txn.employee_id
            has_issue = any(txn.id in f.transaction_ids for f in universe.findings)
            
            G.add_node("COMPANY", node_type="company", color="#3b82f6")
            G.add_node(emp_name, node_type="employee",
                      color="#dc2626" if has_issue else "#22c55e")
            G.add_edge("COMPANY", emp_name,
                      amount=float(txn.net_pay),
                      has_issue=has_issue)
    
    if len(G.nodes()) == 0:
        st.info("No transactions to visualize")
        return
    
    pos = nx.spring_layout(G, k=2, iterations=50)
    
    # Edge traces
    edge_traces = []
    for edge in G.edges(data=True):
        x0, y0 = pos[edge[0]]
        x1, y1 = pos[edge[1]]
        color = '#dc2626' if edge[2].get('has_issue') else '#22c55e'
        
        edge_trace = go.Scatter(
            x=[x0, x1, None], y=[y0, y1, None],
            mode='lines',
            line=dict(width=2, color=color),
            hoverinfo='text',
            text=f"${edge[2].get('amount', 0):,.2f}"
        )
        edge_traces.append(edge_trace)
    
    # Node trace
    node_x, node_y, node_text, node_color = [], [], [], []
    for node in G.nodes(data=True):
        x, y = pos[node[0]]
        node_x.append(x)
        node_y.append(y)
        node_text.append(node[0])
        node_color.append(node[1].get('color', '#6b7280'))
    
    node_trace = go.Scatter(
        x=node_x, y=node_y,
        mode='markers+text',
        hoverinfo='text',
        text=node_text,
        textposition="top center",
        marker=dict(size=30, color=node_color, line=dict(width=2, color='white'))
    )
    
    fig = go.Figure(data=edge_traces + [node_trace])
    fig.update_layout(
        showlegend=False, hovermode='closest', height=500,
        paper_bgcolor='rgba(0,0,0,0)', plot_bgcolor='rgba(0,0,0,0)',
        xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        yaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        font=dict(color='white')
    )
    
    st.plotly_chart(fig, use_container_width=True)
    st.caption("🟢 Clean | 🔴 Has findings | 🔵 Company")


def render_related_party_static(findings, universe):
    """Static fallback for related party network using Plotly."""
    G = nx.Graph()
    
    for f in findings:
        emp_id = None
        vendor_id = None
        for eid in f.entity_ids:
            if eid.startswith('EMP'):
                emp_id = eid
            elif eid.startswith('V'):
                vendor_id = eid
        
        if emp_id and vendor_id:
            emp = universe.employees.get(emp_id)
            vendor = universe.vendors.get(vendor_id)
            
            emp_name = f"👤 {emp.name}" if emp else emp_id
            vendor_name = f"🏪 {vendor.name}" if vendor else vendor_id
            
            G.add_node(emp_name, color="#3b82f6")
            G.add_node(vendor_name, color="#f59e0b")
            G.add_edge(emp_name, vendor_name)
    
    if len(G.nodes()) == 0:
        return
    
    pos = nx.spring_layout(G, k=3)
    
    edge_x, edge_y = [], []
    for edge in G.edges():
        x0, y0 = pos[edge[0]]
        x1, y1 = pos[edge[1]]
        edge_x.extend([x0, x1, None])
        edge_y.extend([y0, y1, None])
    
    edge_trace = go.Scatter(
        x=edge_x, y=edge_y,
        mode='lines',
        line=dict(width=3, color='#dc2626'),
        hoverinfo='none'
    )
    
    node_x = [pos[n][0] for n in G.nodes()]
    node_y = [pos[n][1] for n in G.nodes()]
    node_text = list(G.nodes())
    node_colors = [G.nodes[n].get('color', '#6b7280') for n in G.nodes()]
    
    node_trace = go.Scatter(
        x=node_x, y=node_y,
        mode='markers+text',
        text=node_text,
        textposition="top center",
        hoverinfo='text',
        marker=dict(size=25, color=node_colors, line=dict(width=2, color='white'))
    )
    
    fig = go.Figure(data=[edge_trace, node_trace])
    fig.update_layout(
        title="⚠️ Related Party Connections",
        showlegend=False, height=400,
        paper_bgcolor='rgba(0,0,0,0)', plot_bgcolor='rgba(0,0,0,0)',
        xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        yaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        font=dict(color='white')
    )
    
    st.plotly_chart(fig, use_container_width=True)
    st.caption("🔵 Employee | 🟠 Vendor | 🔴 Connection = Related Party Issue")


def render_related_party_network():
    """Render related party connections as HTML table."""
    if 'universe' not in st.session_state or 'audit_results' not in st.session_state:
        return
    
    results = st.session_state.audit_results
    findings = results.get('related_party_findings', [])
    
    if not findings:
        st.info("No related party issues to visualize")
        return
    
    st.subheader("🔗 Related Party Connections")
    
    universe = st.session_state.universe
    
    # Build HTML table
    html = '''
    <style>
        .rp-table {
            width: 100%;
            border-collapse: collapse;
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            margin: 10px 0;
        }
        .rp-table th {
            background: #1e293b;
            color: #e2e8f0;
            padding: 12px;
            text-align: left;
            border: 1px solid #334155;
            font-weight: 600;
        }
        .rp-table td {
            padding: 12px;
            border: 1px solid #334155;
            color: #f1f5f9;
            background: #0f172a;
        }
        .rp-table tr:hover td {
            background: #1e293b;
        }
        .severity-critical {
            background: #991b1b !important;
            color: white;
            font-weight: bold;
            text-align: center;
        }
        .severity-high {
            background: #c2410c !important;
            color: white;
            font-weight: bold;
            text-align: center;
        }
        .emp-cell {
            color: #60a5fa;
            font-weight: 600;
        }
        .vendor-cell {
            color: #fbbf24;
            font-weight: 600;
        }
        .desc-cell {
            color: #cbd5e1;
            font-size: 13px;
        }
        .rec-cell {
            color: #94a3b8;
            font-size: 12px;
            font-style: italic;
        }
    </style>
    <table class="rp-table">
        <thead>
            <tr>
                <th>Severity</th>
                <th>👤 Employee</th>
                <th>🔗</th>
                <th>🏪 Vendor</th>
                <th>Issue</th>
                <th>Recommendation</th>
            </tr>
        </thead>
        <tbody>
    '''
    
    for f in findings:
        emp_id = None
        vendor_id = None
        for eid in f.entity_ids:
            if eid.startswith('EMP'):
                emp_id = eid
            elif eid.startswith('V'):
                vendor_id = eid
        
        if emp_id and vendor_id:
            emp = universe.employees.get(emp_id)
            vendor = universe.vendors.get(vendor_id)
            
            emp_name = emp.name if emp else emp_id
            emp_title = emp.title if emp else ''
            emp_dept = emp.department if emp else ''
            
            vendor_name = vendor.name if vendor else vendor_id
            
            severity_class = 'severity-critical' if f.severity.value == 'critical' else 'severity-high'
            
            html += f'''
            <tr>
                <td class="{severity_class}">{f.severity.value.upper()}</td>
                <td class="emp-cell">{emp_name}<br><span style="color:#94a3b8;font-size:11px;">{emp_title} - {emp_dept}</span></td>
                <td style="text-align:center;color:#dc2626;font-size:20px;">⟷</td>
                <td class="vendor-cell">{vendor_name}</td>
                <td class="desc-cell">{f.description}</td>
                <td class="rec-cell">{f.recommendation}</td>
            </tr>
            '''
    
    html += '''
        </tbody>
    </table>
    '''
    
    # Calculate height
    table_height = min(400, 80 + len(findings) * 80)
    
    components.html(html, height=table_height, scrolling=True)
    
    st.markdown("""
    **Legend:** 
    🔵 Employee (blue) ⟷ 🟠 Vendor (yellow) = Potential conflict of interest
    """)


# =============================================================================
# MAIN APP
# =============================================================================

def main():
    render_header()
    render_sidebar()
    
    if 'universe' not in st.session_state:
        st.info("👈 Load a dataset from the sidebar to begin")
        
        st.markdown("""
        ## How UCF/GUTT Audit Works
        
        ### The Relational Approach
        
        Traditional audit: "Check if PO exists" ✓/✗
        
        **UCF/GUTT audit:** Analyze **relationships** across multiple **channels**:
        
        | Channel | What it captures |
        |---------|-----------------|
        | Documentation | Do supporting docs exist and match? |
        | Authorization | Was proper approval obtained? |
        | Timing | Is the sequence logical? |
        | Amount | Do figures reconcile? |
        | Counterparty | Is the vendor/customer legitimate? |
        | Segregation | Are duties properly separated? |
        
        ### R_conflict = Audit Finding
        
        When channels send **mixed signals**, that's a finding:
        - Documentation exists ✓ but Authorization missing ✗ → **Conflict**
        - Amount matches ✓ but Timing is wrong ✗ → **Conflict**
        
        ### SOX Control Mapping
        
        Each finding maps to SOX control categories:
        - **Segregation of Duties** - No single person controls entire transaction
        - **Authorization Limits** - Approvals within delegated authority
        - **Management Review** - Appropriate oversight
        - **Reconciliation** - Amounts verified and matched
        - **Documentation** - Adequate support retained
        """)
        return
    
    if not st.session_state.get('audit_run'):
        st.warning("👈 Click 'Run Full Audit' to analyze the data")
        
        # Show data preview
        universe = st.session_state.universe
        
        tab1, tab2, tab3, tab4 = st.tabs(["AP Preview", "AR Preview", "Payroll Preview", "GL Preview"])
        
        with tab1:
            if universe.ap_transactions:
                data = []
                for txn in universe.ap_transactions.values():
                    vendor = universe.vendors.get(txn.vendor_id)
                    data.append({
                        'ID': txn.id,
                        'Vendor': vendor.name if vendor else txn.vendor_id,
                        'PO': txn.po_number or "❌ MISSING",
                        'Invoice': txn.invoice_number or "❌ MISSING",
                        'PO Amount': f"${txn.po_amount:,.2f}",
                        'Invoice Amount': f"${txn.invoice_amount:,.2f}",
                        'Payment': f"${txn.payment_amount:,.2f}",
                    })
                st.dataframe(pd.DataFrame(data), use_container_width=True)
        
        with tab2:
            if universe.ar_transactions:
                data = []
                for txn in universe.ar_transactions.values():
                    customer = universe.customers.get(txn.customer_id)
                    data.append({
                        'ID': txn.id,
                        'Customer': customer.name if customer else txn.customer_id,
                        'Invoice': txn.invoice_number,
                        'Amount': f"${txn.invoice_amount:,.2f}",
                        'Received': f"${txn.payment_received:,.2f}",
                        'Balance': f"${txn.balance_due():,.2f}",
                        'Days Out': txn.days_outstanding(),
                    })
                st.dataframe(pd.DataFrame(data), use_container_width=True)
        
        with tab3:
            if universe.payroll_transactions:
                data = []
                for txn in universe.payroll_transactions.values():
                    emp = universe.employees.get(txn.employee_id)
                    data.append({
                        'ID': txn.id,
                        'Employee': emp.name if emp else txn.employee_id,
                        'Period': f"{txn.pay_period_start} - {txn.pay_period_end}",
                        'Reg Hours': float(txn.regular_hours),
                        'OT Hours': float(txn.overtime_hours),
                        'Gross': f"${txn.gross_pay:,.2f}",
                        'Net': f"${txn.net_pay:,.2f}",
                        'Timesheet': "✓" if txn.has_timesheet else "❌",
                    })
                st.dataframe(pd.DataFrame(data), use_container_width=True)
        
        with tab4:
            if universe.journal_entries:
                data = []
                for entry in universe.journal_entries.values():
                    data.append({
                        'ID': entry.id,
                        'Date': entry.posting_date,
                        'Description': entry.description[:40] + "..." if len(entry.description) > 40 else entry.description,
                        'Debits': f"${entry.total_debits():,.2f}",
                        'Credits': f"${entry.total_credits():,.2f}",
                        'Balanced': "✓" if entry.is_balanced() else "❌",
                        'Manual': "Yes" if entry.is_manual else "No",
                        'Approved': entry.approved_by or "❌",
                    })
                st.dataframe(pd.DataFrame(data), use_container_width=True)
        
        return
    
    # Audit has been run - show results
    results = st.session_state.audit_results
    health_score = st.session_state.health_score
    
    # Tabs for different views
    (tab_summary, tab_ap, tab_ar, tab_payroll, tab_gl, 
     tab_ap_data, tab_ar_data, tab_payroll_data, tab_gl_data, tab_master,
     tab_related, tab_network, tab_matrix) = st.tabs([
        "📋 Summary", 
        "💳 AP Findings", 
        "💰 AR Findings", 
        "👷 Payroll Findings", 
        "📒 GL Findings",
        "📊 AP Data",
        "📊 AR Data", 
        "📊 Payroll Data",
        "📊 GL Data",
        "📊 Master Data",
        "👥 Related Party",
        "🕸️ Network",
        "🔲 Control Matrix"
    ])
    
    universe = st.session_state.universe
    
    with tab_summary:
        render_executive_summary(results, health_score)
    
    with tab_ap:
        render_findings_by_domain(results, 'ap', "💳 Accounts Payable Findings")
    
    with tab_ar:
        render_findings_by_domain(results, 'ar', "💰 Accounts Receivable Findings")
    
    with tab_payroll:
        render_findings_by_domain(results, 'payroll', "👷 Payroll Findings")
    
    with tab_gl:
        render_findings_by_domain(results, 'gl', "📒 General Ledger Findings")
    
    with tab_ap_data:
        render_ap_data(universe)
    
    with tab_ar_data:
        render_ar_data(universe)
    
    with tab_payroll_data:
        render_payroll_data(universe)
    
    with tab_gl_data:
        render_gl_data(universe)
    
    with tab_master:
        render_master_data(universe)
    
    with tab_related:
        render_related_parties(results)
        st.markdown("---")
        render_related_party_network()
    
    with tab_network:
        st.header("🕸️ Transaction Flow Visualization")
        st.markdown("""
        Visualize money flow and identify problematic transactions.
        - 🟢 **Green nodes/edges**: Clean transactions
        - 🔴 **Red nodes/edges**: Transactions with findings
        - 🔵 **Blue**: Company (central node)
        """)
        render_transaction_network()
    
    with tab_matrix:
        st.header("🔲 Control Channel Matrix")
        st.markdown("""
        Interactive heatmap showing control compliance by channel.
        **Hover over cells** to see details about each control test.
        """)
        
        domain_select = st.selectbox(
            "Select Domain",
            [TransactionDomain.AP, TransactionDomain.AR, TransactionDomain.PAYROLL],
            format_func=lambda x: x.value.replace("_", " ").title()
        )
        
        render_channel_heatmap(domain_select)
    
    # Footer
    st.markdown("---")
    st.markdown("""
    <div style="text-align: center; color: #64748b; font-size: 12px;">
        UCF/GUTT™ Audit Framework — Enhanced Demo (SOX Compliance)<br>
        © 2023-2026 Michael Fillippini. All Rights Reserved.<br>
        <a href="mailto:Michael_Fill@ProtonMail.com">License full version</a>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    main()
