"""
UCF/GUTT Audit Framework - Analysis Module
==========================================

DEMONSTRATION VERSION - Simplified algorithms for concept illustration.
Production system uses proprietary UCF/GUTT tensor analysis.

Copyright (c) 2026 Michael Fillippini. All Rights Reserved.

SOX Control Testing:
- Segregation of duties
- Authorization limits  
- Management review
- Documentation requirements
- Reconciliation controls
"""

from typing import Dict, List, Optional, Tuple
from decimal import Decimal
from datetime import date, timedelta
from dataclasses import dataclass
import uuid

from audit_core import (
    AuditUniverse, AuditFinding, AuditRelationalTensor,
    TransactionDomain, SOXControl, FindingSeverity,
    APChannel, ARChannel, PayrollChannel, GLChannel,
    APTransaction, ARTransaction, PayrollTransaction, JournalEntry,
    Vendor, Employee, RelatedPartyType
)


__version__ = "DEMO-1.0"
__author__ = "Michael Fillippini"


# =============================================================================
# AP ANALYSIS
# =============================================================================

class APAnalyzer:
    """
    DEMO: Accounts Payable analysis.
    
    Tests:
    - 3-way match (PO, Invoice, Payment)
    - Proper authorization
    - Segregation of duties
    - Timing sequence
    - Vendor legitimacy
    """
    
    def __init__(self, universe: AuditUniverse):
        self.universe = universe
        self.tensor = universe.ap_tensor
    
    def analyze_transaction(self, txn: APTransaction) -> List[AuditFinding]:
        """Analyze single AP transaction and populate tensor."""
        findings = []
        vendor = self.universe.vendors.get(txn.vendor_id)
        
        # Channel: Documentation
        if not txn.po_number:
            self.tensor.set_weight(APChannel.DOCUMENTATION.value, txn.id, txn.vendor_id, -0.8)
            findings.append(AuditFinding(
                id=f"AP-DOC-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AP,
                severity=FindingSeverity.HIGH,
                sox_control=SOXControl.DOCUMENTATION,
                title="Missing Purchase Order",
                description=f"Payment to {vendor.name if vendor else txn.vendor_id} without PO",
                transaction_ids=[txn.id],
                entity_ids=[txn.vendor_id],
                channel_violations={APChannel.DOCUMENTATION.value: -0.8},
                recommendation="Implement mandatory PO requirement for all purchases"
            ))
        elif not txn.invoice_number:
            self.tensor.set_weight(APChannel.DOCUMENTATION.value, txn.id, txn.vendor_id, -0.5)
            findings.append(AuditFinding(
                id=f"AP-DOC-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AP,
                severity=FindingSeverity.MEDIUM,
                sox_control=SOXControl.DOCUMENTATION,
                title="Missing Invoice",
                description=f"Payment to {vendor.name if vendor else txn.vendor_id} without invoice on file",
                transaction_ids=[txn.id],
                entity_ids=[txn.vendor_id],
                channel_violations={APChannel.DOCUMENTATION.value: -0.5},
                recommendation="Require invoice matching before payment processing"
            ))
        else:
            self.tensor.set_weight(APChannel.DOCUMENTATION.value, txn.id, txn.vendor_id, 1.0)
        
        # Channel: Amount (3-way match)
        match_ok, match_msg = txn.three_way_match()
        if not match_ok:
            self.tensor.set_weight(APChannel.AMOUNT.value, txn.id, txn.vendor_id, -0.9)
            findings.append(AuditFinding(
                id=f"AP-AMT-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AP,
                severity=FindingSeverity.HIGH,
                sox_control=SOXControl.RECONCILIATION,
                title="3-Way Match Failure",
                description=f"{match_msg} for vendor {vendor.name if vendor else txn.vendor_id}",
                transaction_ids=[txn.id],
                entity_ids=[txn.vendor_id],
                channel_violations={APChannel.AMOUNT.value: -0.9},
                recommendation="Investigate variance and implement automated matching"
            ))
        else:
            self.tensor.set_weight(APChannel.AMOUNT.value, txn.id, txn.vendor_id, 1.0)
        
        # Channel: Authorization
        if not txn.po_approved_by:
            self.tensor.set_weight(APChannel.AUTHORIZATION.value, txn.id, txn.vendor_id, -0.7)
            findings.append(AuditFinding(
                id=f"AP-AUTH-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AP,
                severity=FindingSeverity.HIGH,
                sox_control=SOXControl.AUTHORIZATION,
                title="Missing PO Approval",
                description=f"Purchase order not approved for {vendor.name if vendor else txn.vendor_id}",
                transaction_ids=[txn.id],
                entity_ids=[txn.vendor_id],
                channel_violations={APChannel.AUTHORIZATION.value: -0.7},
                recommendation="Enforce approval workflow before PO issuance"
            ))
        elif not txn.payment_approved_by:
            self.tensor.set_weight(APChannel.AUTHORIZATION.value, txn.id, txn.vendor_id, -0.6)
            findings.append(AuditFinding(
                id=f"AP-AUTH-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AP,
                severity=FindingSeverity.MEDIUM,
                sox_control=SOXControl.AUTHORIZATION,
                title="Missing Payment Approval",
                description=f"Payment not approved for {vendor.name if vendor else txn.vendor_id}",
                transaction_ids=[txn.id],
                entity_ids=[txn.vendor_id],
                channel_violations={APChannel.AUTHORIZATION.value: -0.6},
                recommendation="Require payment approval before disbursement"
            ))
        else:
            # Check authorization limit
            approver = self.universe.employees.get(txn.payment_approved_by)
            if approver and approver.authorization_limit > 0:
                if txn.payment_amount > approver.authorization_limit:
                    self.tensor.set_weight(APChannel.AUTHORIZATION.value, txn.id, txn.vendor_id, -0.8)
                    findings.append(AuditFinding(
                        id=f"AP-AUTH-{uuid.uuid4().hex[:8]}",
                        domain=TransactionDomain.AP,
                        severity=FindingSeverity.CRITICAL,
                        sox_control=SOXControl.AUTHORIZATION,
                        title="Authorization Limit Exceeded",
                        description=f"{approver.name} approved ${txn.payment_amount} but limit is ${approver.authorization_limit}",
                        transaction_ids=[txn.id],
                        entity_ids=[txn.vendor_id, approver.id],
                        channel_violations={APChannel.AUTHORIZATION.value: -0.8},
                        recommendation="Escalate to higher authority for approval"
                    ))
                else:
                    self.tensor.set_weight(APChannel.AUTHORIZATION.value, txn.id, txn.vendor_id, 1.0)
            else:
                self.tensor.set_weight(APChannel.AUTHORIZATION.value, txn.id, txn.vendor_id, 0.8)
        
        # Channel: Timing
        timing_ok = True
        timing_issues = []
        
        if txn.po_date and txn.invoice_date:
            if txn.invoice_date < txn.po_date:
                timing_issues.append("Invoice dated before PO")
                timing_ok = False
        
        if txn.invoice_date and txn.payment_date:
            if txn.payment_date < txn.invoice_date:
                timing_issues.append("Payment before invoice")
                timing_ok = False
        
        if timing_ok:
            self.tensor.set_weight(APChannel.TIMING.value, txn.id, txn.vendor_id, 1.0)
        else:
            self.tensor.set_weight(APChannel.TIMING.value, txn.id, txn.vendor_id, -0.7)
            findings.append(AuditFinding(
                id=f"AP-TIME-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AP,
                severity=FindingSeverity.MEDIUM,
                sox_control=SOXControl.DOCUMENTATION,
                title="Transaction Timing Anomaly",
                description=f"{'; '.join(timing_issues)} for {vendor.name if vendor else txn.vendor_id}",
                transaction_ids=[txn.id],
                entity_ids=[txn.vendor_id],
                channel_violations={APChannel.TIMING.value: -0.7},
                recommendation="Investigate backdating or data entry errors"
            ))
        
        # Channel: Segregation of Duties
        seg_violations = []
        
        if txn.po_created_by and txn.po_approved_by:
            if txn.po_created_by == txn.po_approved_by:
                seg_violations.append("PO creator approved own PO")
        
        if txn.po_approved_by and txn.payment_approved_by:
            if txn.po_approved_by == txn.payment_approved_by:
                seg_violations.append("Same person approved PO and payment")
        
        if txn.payment_approved_by and txn.payment_processed_by:
            if txn.payment_approved_by == txn.payment_processed_by:
                seg_violations.append("Same person approved and processed payment")
        
        if seg_violations:
            self.tensor.set_weight(APChannel.SEGREGATION.value, txn.id, txn.vendor_id, -0.9)
            findings.append(AuditFinding(
                id=f"AP-SEG-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AP,
                severity=FindingSeverity.CRITICAL,
                sox_control=SOXControl.SEGREGATION,
                title="Segregation of Duties Violation",
                description=f"{'; '.join(seg_violations)}",
                transaction_ids=[txn.id],
                entity_ids=[txn.vendor_id],
                channel_violations={APChannel.SEGREGATION.value: -0.9},
                recommendation="Implement proper segregation - no single person should control entire transaction"
            ))
        else:
            self.tensor.set_weight(APChannel.SEGREGATION.value, txn.id, txn.vendor_id, 1.0)
        
        # Channel: Counterparty (Vendor)
        if vendor:
            if not vendor.is_active:
                self.tensor.set_weight(APChannel.COUNTERPARTY.value, txn.id, txn.vendor_id, -0.8)
                findings.append(AuditFinding(
                    id=f"AP-VND-{uuid.uuid4().hex[:8]}",
                    domain=TransactionDomain.AP,
                    severity=FindingSeverity.HIGH,
                    sox_control=SOXControl.AUTHORIZATION,
                    title="Payment to Inactive Vendor",
                    description=f"Payment to inactive vendor {vendor.name}",
                    transaction_ids=[txn.id],
                    entity_ids=[txn.vendor_id],
                    channel_violations={APChannel.COUNTERPARTY.value: -0.8},
                    recommendation="Review vendor status before payment"
                ))
            elif not vendor.approved_by:
                self.tensor.set_weight(APChannel.COUNTERPARTY.value, txn.id, txn.vendor_id, -0.5)
                findings.append(AuditFinding(
                    id=f"AP-VND-{uuid.uuid4().hex[:8]}",
                    domain=TransactionDomain.AP,
                    severity=FindingSeverity.MEDIUM,
                    sox_control=SOXControl.AUTHORIZATION,
                    title="Unapproved Vendor",
                    description=f"Vendor {vendor.name} not formally approved",
                    transaction_ids=[txn.id],
                    entity_ids=[txn.vendor_id],
                    channel_violations={APChannel.COUNTERPARTY.value: -0.5},
                    recommendation="Implement vendor approval process"
                ))
            else:
                self.tensor.set_weight(APChannel.COUNTERPARTY.value, txn.id, txn.vendor_id, 1.0)
        else:
            self.tensor.set_weight(APChannel.COUNTERPARTY.value, txn.id, txn.vendor_id, -1.0)
            findings.append(AuditFinding(
                id=f"AP-VND-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AP,
                severity=FindingSeverity.CRITICAL,
                sox_control=SOXControl.AUTHORIZATION,
                title="Unknown Vendor",
                description=f"Payment to unregistered vendor ID: {txn.vendor_id}",
                transaction_ids=[txn.id],
                entity_ids=[txn.vendor_id],
                channel_violations={APChannel.COUNTERPARTY.value: -1.0},
                recommendation="Investigate - possible fraudulent vendor"
            ))
        
        return findings
    
    def analyze_all(self) -> List[AuditFinding]:
        """Analyze all AP transactions."""
        all_findings = []
        for txn in self.universe.ap_transactions.values():
            all_findings.extend(self.analyze_transaction(txn))
        return all_findings


# =============================================================================
# AR ANALYSIS
# =============================================================================

class ARAnalyzer:
    """
    DEMO: Accounts Receivable analysis.
    
    Tests:
    - Aging analysis
    - Credit limit compliance
    - Write-off authorization
    - Credit memo approval
    """
    
    def __init__(self, universe: AuditUniverse):
        self.universe = universe
        self.tensor = universe.ar_tensor
    
    def analyze_transaction(self, txn: ARTransaction) -> List[AuditFinding]:
        """Analyze single AR transaction."""
        findings = []
        customer = self.universe.customers.get(txn.customer_id)
        
        # Channel: Documentation
        if txn.invoice_created_by:
            self.tensor.set_weight(ARChannel.DOCUMENTATION.value, txn.id, txn.customer_id, 1.0)
        else:
            self.tensor.set_weight(ARChannel.DOCUMENTATION.value, txn.id, txn.customer_id, -0.5)
        
        # Channel: Authorization - Write-offs
        if txn.write_off_amount > 0 and not txn.write_off_approved_by:
            self.tensor.set_weight(ARChannel.AUTHORIZATION.value, txn.id, txn.customer_id, -0.9)
            findings.append(AuditFinding(
                id=f"AR-AUTH-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AR,
                severity=FindingSeverity.CRITICAL,
                sox_control=SOXControl.AUTHORIZATION,
                title="Unapproved Write-Off",
                description=f"Write-off of ${txn.write_off_amount} without approval for {customer.name if customer else txn.customer_id}",
                transaction_ids=[txn.id],
                entity_ids=[txn.customer_id],
                channel_violations={ARChannel.AUTHORIZATION.value: -0.9},
                recommendation="Require management approval for all write-offs"
            ))
        
        # Credit memo approval
        if txn.credit_memo_amount > 0 and not txn.credit_memo_approved_by:
            self.tensor.set_weight(ARChannel.AUTHORIZATION.value, txn.id, txn.customer_id, -0.7)
            findings.append(AuditFinding(
                id=f"AR-AUTH-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AR,
                severity=FindingSeverity.HIGH,
                sox_control=SOXControl.AUTHORIZATION,
                title="Unapproved Credit Memo",
                description=f"Credit memo of ${txn.credit_memo_amount} without approval",
                transaction_ids=[txn.id],
                entity_ids=[txn.customer_id],
                channel_violations={ARChannel.AUTHORIZATION.value: -0.7},
                recommendation="Require approval for credit memos"
            ))
        else:
            self.tensor.set_weight(ARChannel.AUTHORIZATION.value, txn.id, txn.customer_id, 1.0)
        
        # Channel: Timing (Aging)
        days = txn.days_outstanding()
        if days > 90:
            self.tensor.set_weight(ARChannel.TIMING.value, txn.id, txn.customer_id, -0.8)
            findings.append(AuditFinding(
                id=f"AR-AGE-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AR,
                severity=FindingSeverity.MEDIUM,
                sox_control=SOXControl.MANAGEMENT_REVIEW,
                title="Severely Aged Receivable",
                description=f"Invoice {txn.invoice_number} is {days} days old (${txn.balance_due()} outstanding)",
                transaction_ids=[txn.id],
                entity_ids=[txn.customer_id],
                channel_violations={ARChannel.TIMING.value: -0.8},
                recommendation="Escalate collection efforts or evaluate for write-off"
            ))
        elif days > 60:
            self.tensor.set_weight(ARChannel.TIMING.value, txn.id, txn.customer_id, -0.4)
        else:
            self.tensor.set_weight(ARChannel.TIMING.value, txn.id, txn.customer_id, 1.0)
        
        # Channel: Customer (Credit limit)
        if customer:
            # Check if customer exceeded credit limit
            total_outstanding = sum(
                t.balance_due() for t in self.universe.ar_transactions.values()
                if t.customer_id == customer.id
            )
            if customer.credit_limit > 0 and total_outstanding > customer.credit_limit:
                self.tensor.set_weight(ARChannel.CUSTOMER.value, txn.id, txn.customer_id, -0.6)
                findings.append(AuditFinding(
                    id=f"AR-CRD-{uuid.uuid4().hex[:8]}",
                    domain=TransactionDomain.AR,
                    severity=FindingSeverity.MEDIUM,
                    sox_control=SOXControl.AUTHORIZATION,
                    title="Credit Limit Exceeded",
                    description=f"{customer.name} has ${total_outstanding} outstanding vs ${customer.credit_limit} limit",
                    transaction_ids=[txn.id],
                    entity_ids=[txn.customer_id],
                    channel_violations={ARChannel.CUSTOMER.value: -0.6},
                    recommendation="Place customer on credit hold"
                ))
            else:
                self.tensor.set_weight(ARChannel.CUSTOMER.value, txn.id, txn.customer_id, 1.0)
        
        return findings
    
    def analyze_all(self) -> List[AuditFinding]:
        """Analyze all AR transactions."""
        all_findings = []
        for txn in self.universe.ar_transactions.values():
            all_findings.extend(self.analyze_transaction(txn))
        return all_findings


# =============================================================================
# PAYROLL ANALYSIS
# =============================================================================

class PayrollAnalyzer:
    """
    DEMO: Payroll analysis.
    
    Tests:
    - Ghost employee detection
    - Timesheet approval
    - Pay calculation accuracy
    - Segregation of duties
    """
    
    def __init__(self, universe: AuditUniverse):
        self.universe = universe
        self.tensor = universe.payroll_tensor
    
    def analyze_transaction(self, txn: PayrollTransaction) -> List[AuditFinding]:
        """Analyze single payroll transaction."""
        findings = []
        employee = self.universe.employees.get(txn.employee_id)
        
        # Channel: Employee (exists and active)
        if not employee:
            self.tensor.set_weight(PayrollChannel.EMPLOYEE.value, txn.id, txn.employee_id, -1.0)
            findings.append(AuditFinding(
                id=f"PAY-EMP-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.PAYROLL,
                severity=FindingSeverity.CRITICAL,
                sox_control=SOXControl.AUTHORIZATION,
                title="Possible Ghost Employee",
                description=f"Payment to unknown employee ID: {txn.employee_id}",
                transaction_ids=[txn.id],
                entity_ids=[txn.employee_id],
                channel_violations={PayrollChannel.EMPLOYEE.value: -1.0},
                recommendation="Investigate immediately - potential fraud"
            ))
        elif not employee.is_active(txn.pay_period_end):
            self.tensor.set_weight(PayrollChannel.EMPLOYEE.value, txn.id, txn.employee_id, -0.9)
            findings.append(AuditFinding(
                id=f"PAY-EMP-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.PAYROLL,
                severity=FindingSeverity.CRITICAL,
                sox_control=SOXControl.AUTHORIZATION,
                title="Payment to Terminated Employee",
                description=f"Payment to {employee.name} after termination date {employee.termination_date}",
                transaction_ids=[txn.id],
                entity_ids=[txn.employee_id],
                channel_violations={PayrollChannel.EMPLOYEE.value: -0.9},
                recommendation="Stop payment and recover funds"
            ))
        else:
            self.tensor.set_weight(PayrollChannel.EMPLOYEE.value, txn.id, txn.employee_id, 1.0)
        
        # Channel: Documentation (Timesheet)
        if txn.regular_hours > 0 or txn.overtime_hours > 0:
            if not txn.has_timesheet:
                self.tensor.set_weight(PayrollChannel.DOCUMENTATION.value, txn.id, txn.employee_id, -0.7)
                findings.append(AuditFinding(
                    id=f"PAY-DOC-{uuid.uuid4().hex[:8]}",
                    domain=TransactionDomain.PAYROLL,
                    severity=FindingSeverity.HIGH,
                    sox_control=SOXControl.DOCUMENTATION,
                    title="Missing Timesheet",
                    description=f"Payment for {txn.regular_hours + txn.overtime_hours} hours without timesheet",
                    transaction_ids=[txn.id],
                    entity_ids=[txn.employee_id],
                    channel_violations={PayrollChannel.DOCUMENTATION.value: -0.7},
                    recommendation="Require timesheet submission for all hourly payments"
                ))
            else:
                self.tensor.set_weight(PayrollChannel.DOCUMENTATION.value, txn.id, txn.employee_id, 1.0)
        
        # Channel: Authorization (Timesheet approval)
        if txn.overtime_hours > 0 and not txn.timesheet_approved_by:
            self.tensor.set_weight(PayrollChannel.AUTHORIZATION.value, txn.id, txn.employee_id, -0.8)
            findings.append(AuditFinding(
                id=f"PAY-AUTH-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.PAYROLL,
                severity=FindingSeverity.HIGH,
                sox_control=SOXControl.AUTHORIZATION,
                title="Unapproved Overtime",
                description=f"{txn.overtime_hours} overtime hours without approval",
                transaction_ids=[txn.id],
                entity_ids=[txn.employee_id],
                channel_violations={PayrollChannel.AUTHORIZATION.value: -0.8},
                recommendation="Require manager approval for overtime"
            ))
        else:
            self.tensor.set_weight(PayrollChannel.AUTHORIZATION.value, txn.id, txn.employee_id, 1.0)
        
        # Channel: Amount (calculation accuracy)
        if txn.hourly_rate > 0:
            variance = txn.gross_variance()
            if variance > Decimal("0.01"):
                self.tensor.set_weight(PayrollChannel.AMOUNT.value, txn.id, txn.employee_id, -0.7)
                findings.append(AuditFinding(
                    id=f"PAY-AMT-{uuid.uuid4().hex[:8]}",
                    domain=TransactionDomain.PAYROLL,
                    severity=FindingSeverity.MEDIUM,
                    sox_control=SOXControl.RECONCILIATION,
                    title="Pay Calculation Variance",
                    description=f"Gross pay ${txn.gross_pay} vs calculated ${txn.calculated_gross()} (diff: ${variance})",
                    transaction_ids=[txn.id],
                    entity_ids=[txn.employee_id],
                    channel_violations={PayrollChannel.AMOUNT.value: -0.7},
                    recommendation="Verify pay calculation and adjust if necessary"
                ))
            else:
                self.tensor.set_weight(PayrollChannel.AMOUNT.value, txn.id, txn.employee_id, 1.0)
        
        # Check net pay = gross - deductions
        if txn.gross_pay > 0:
            expected_net = txn.gross_pay - txn.deductions
            if abs(txn.net_pay - expected_net) > Decimal("0.01"):
                self.tensor.set_weight(PayrollChannel.AMOUNT.value, txn.id, txn.employee_id, -0.6)
                findings.append(AuditFinding(
                    id=f"PAY-AMT-{uuid.uuid4().hex[:8]}",
                    domain=TransactionDomain.PAYROLL,
                    severity=FindingSeverity.MEDIUM,
                    sox_control=SOXControl.RECONCILIATION,
                    title="Net Pay Calculation Error",
                    description=f"Net pay ${txn.net_pay} ≠ Gross ${txn.gross_pay} - Deductions ${txn.deductions}",
                    transaction_ids=[txn.id],
                    entity_ids=[txn.employee_id],
                    channel_violations={PayrollChannel.AMOUNT.value: -0.6},
                    recommendation="Review payroll calculation"
                ))
        
        # Channel: Segregation
        if employee and txn.timesheet_approved_by:
            # Manager can't approve own timesheet
            if txn.employee_id == txn.timesheet_approved_by:
                self.tensor.set_weight(PayrollChannel.SEGREGATION.value, txn.id, txn.employee_id, -0.9)
                findings.append(AuditFinding(
                    id=f"PAY-SEG-{uuid.uuid4().hex[:8]}",
                    domain=TransactionDomain.PAYROLL,
                    severity=FindingSeverity.CRITICAL,
                    sox_control=SOXControl.SEGREGATION,
                    title="Self-Approved Timesheet",
                    description=f"Employee approved their own timesheet",
                    transaction_ids=[txn.id],
                    entity_ids=[txn.employee_id],
                    channel_violations={PayrollChannel.SEGREGATION.value: -0.9},
                    recommendation="Require manager approval for all timesheets"
                ))
            else:
                self.tensor.set_weight(PayrollChannel.SEGREGATION.value, txn.id, txn.employee_id, 1.0)
        
        return findings
    
    def analyze_all(self) -> List[AuditFinding]:
        """Analyze all payroll transactions."""
        all_findings = []
        for txn in self.universe.payroll_transactions.values():
            all_findings.extend(self.analyze_transaction(txn))
        return all_findings


# =============================================================================
# GL ANALYSIS
# =============================================================================

class GLAnalyzer:
    """
    DEMO: General Ledger analysis.
    
    Tests:
    - Journal entry balance
    - Manual entry approval
    - Round amount detection
    - Period-end anomalies
    - Reversing entries
    """
    
    def __init__(self, universe: AuditUniverse):
        self.universe = universe
        self.tensor = universe.gl_tensor
    
    def analyze_entry(self, entry: JournalEntry) -> List[AuditFinding]:
        """Analyze single journal entry."""
        findings = []
        
        # Channel: Balance
        if not entry.is_balanced():
            self.tensor.set_weight(GLChannel.BALANCE.value, entry.id, "GL", -1.0)
            findings.append(AuditFinding(
                id=f"GL-BAL-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.GL,
                severity=FindingSeverity.CRITICAL,
                sox_control=SOXControl.RECONCILIATION,
                title="Unbalanced Journal Entry",
                description=f"Entry {entry.id}: Debits ${entry.total_debits()} ≠ Credits ${entry.total_credits()}",
                transaction_ids=[entry.id],
                channel_violations={GLChannel.BALANCE.value: -1.0},
                recommendation="Correct entry immediately"
            ))
        else:
            self.tensor.set_weight(GLChannel.BALANCE.value, entry.id, "GL", 1.0)
        
        # Channel: Authorization (manual entries)
        if entry.is_manual and not entry.approved_by:
            self.tensor.set_weight(GLChannel.AUTHORIZATION.value, entry.id, "GL", -0.8)
            findings.append(AuditFinding(
                id=f"GL-AUTH-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.GL,
                severity=FindingSeverity.HIGH,
                sox_control=SOXControl.AUTHORIZATION,
                title="Unapproved Manual Entry",
                description=f"Manual journal entry {entry.id} without approval",
                transaction_ids=[entry.id],
                channel_violations={GLChannel.AUTHORIZATION.value: -0.8},
                recommendation="Require approval for all manual journal entries"
            ))
        else:
            self.tensor.set_weight(GLChannel.AUTHORIZATION.value, entry.id, "GL", 1.0)
        
        # Channel: Amount (round numbers - fraud indicator)
        if entry.is_round_amount():
            self.tensor.set_weight(GLChannel.AMOUNT.value, entry.id, "GL", -0.4)
            findings.append(AuditFinding(
                id=f"GL-AMT-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.GL,
                severity=FindingSeverity.LOW,
                sox_control=SOXControl.MANAGEMENT_REVIEW,
                title="Suspiciously Round Amount",
                description=f"Entry {entry.id} contains large round amount(s) - review for legitimacy",
                transaction_ids=[entry.id],
                channel_violations={GLChannel.AMOUNT.value: -0.4},
                recommendation="Review supporting documentation for round amounts"
            ))
        else:
            self.tensor.set_weight(GLChannel.AMOUNT.value, entry.id, "GL", 1.0)
        
        # Channel: Segregation (preparer/reviewer)
        if entry.created_by and entry.approved_by:
            if entry.created_by == entry.approved_by:
                self.tensor.set_weight(GLChannel.SEGREGATION.value, entry.id, "GL", -0.9)
                findings.append(AuditFinding(
                    id=f"GL-SEG-{uuid.uuid4().hex[:8]}",
                    domain=TransactionDomain.GL,
                    severity=FindingSeverity.HIGH,
                    sox_control=SOXControl.SEGREGATION,
                    title="Self-Approved Journal Entry",
                    description=f"Entry {entry.id} created and approved by same person: {entry.created_by}",
                    transaction_ids=[entry.id],
                    channel_violations={GLChannel.SEGREGATION.value: -0.9},
                    recommendation="Require independent review for all journal entries"
                ))
            else:
                self.tensor.set_weight(GLChannel.SEGREGATION.value, entry.id, "GL", 1.0)
        
        # Channel: Timing (period-end)
        # Check if entry is last day of month (period-end entry)
        if entry.posting_date.day >= 28:
            # Check for unusual posting time patterns would go here
            pass
        
        # Documentation
        if entry.description and len(entry.description) > 10:
            self.tensor.set_weight(GLChannel.DOCUMENTATION.value, entry.id, "GL", 1.0)
        else:
            self.tensor.set_weight(GLChannel.DOCUMENTATION.value, entry.id, "GL", -0.3)
            findings.append(AuditFinding(
                id=f"GL-DOC-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.GL,
                severity=FindingSeverity.LOW,
                sox_control=SOXControl.DOCUMENTATION,
                title="Insufficient Entry Description",
                description=f"Entry {entry.id} lacks adequate description",
                transaction_ids=[entry.id],
                channel_violations={GLChannel.DOCUMENTATION.value: -0.3},
                recommendation="Require detailed descriptions for all journal entries"
            ))
        
        return findings
    
    def analyze_all(self) -> List[AuditFinding]:
        """Analyze all journal entries."""
        all_findings = []
        for entry in self.universe.journal_entries.values():
            all_findings.extend(self.analyze_entry(entry))
        return all_findings


# =============================================================================
# MASTER AUDIT ANALYZER
# =============================================================================

class AuditAnalyzer:
    """
    Master analyzer that runs all domain analyzers and related party detection.
    
    DEMO: Simplified algorithms.
    Production includes advanced pattern detection, ML-based anomaly scoring,
    and temporal analysis.
    """
    
    def __init__(self, universe: AuditUniverse):
        self.universe = universe
        self.ap_analyzer = APAnalyzer(universe)
        self.ar_analyzer = ARAnalyzer(universe)
        self.payroll_analyzer = PayrollAnalyzer(universe)
        self.gl_analyzer = GLAnalyzer(universe)
    
    def run_full_audit(self) -> Dict:
        """Run complete audit across all domains."""
        results = {
            'ap_findings': [],
            'ar_findings': [],
            'payroll_findings': [],
            'gl_findings': [],
            'related_party_findings': [],
            'summary': {}
        }
        
        # Run domain analyses
        results['ap_findings'] = self.ap_analyzer.analyze_all()
        results['ar_findings'] = self.ar_analyzer.analyze_all()
        results['payroll_findings'] = self.payroll_analyzer.analyze_all()
        results['gl_findings'] = self.gl_analyzer.analyze_all()
        
        # Run related party detection
        related_parties = self.universe.related_party_detector.detect_all(
            list(self.universe.employees.values()),
            list(self.universe.vendors.values())
        )
        
        # Convert related party matches to findings
        for rp in related_parties:
            finding = AuditFinding(
                id=f"RP-{uuid.uuid4().hex[:8]}",
                domain=TransactionDomain.AP,  # Most relevant
                severity=rp['severity'],
                sox_control=SOXControl.AUTHORIZATION,
                title=f"Related Party: {rp['type'].value}",
                description=rp['details'],
                entity_ids=[rp.get('employee_id', ''), rp.get('vendor_id', '')],
                recommendation="Investigate relationship and implement additional controls"
            )
            results['related_party_findings'].append(finding)
        
        # Store findings in universe
        all_findings = (
            results['ap_findings'] + 
            results['ar_findings'] + 
            results['payroll_findings'] + 
            results['gl_findings'] +
            results['related_party_findings']
        )
        self.universe.findings = all_findings
        
        # Summary
        results['summary'] = self._build_summary(results)
        
        return results
    
    def _build_summary(self, results: Dict) -> Dict:
        """Build audit summary."""
        all_findings = (
            results['ap_findings'] + 
            results['ar_findings'] + 
            results['payroll_findings'] + 
            results['gl_findings'] +
            results['related_party_findings']
        )
        
        severity_counts = {s.value: 0 for s in FindingSeverity}
        sox_counts = {c.value: 0 for c in SOXControl}
        domain_counts = {d.value: 0 for d in TransactionDomain}
        
        for f in all_findings:
            severity_counts[f.severity.value] += 1
            if f.sox_control:
                sox_counts[f.sox_control.value] += 1
            domain_counts[f.domain.value] += 1
        
        return {
            'total_findings': len(all_findings),
            'by_severity': severity_counts,
            'by_sox_control': sox_counts,
            'by_domain': domain_counts,
            'critical_count': severity_counts[FindingSeverity.CRITICAL.value],
            'high_count': severity_counts[FindingSeverity.HIGH.value],
            'related_party_count': len(results['related_party_findings']),
        }
    
    def get_control_health_score(self) -> float:
        """
        DEMO: Simple control health score.
        
        Production uses calibrated multi-factor analysis with
        severity weighting and control interdependencies.
        """
        if not self.universe.findings:
            return 100.0
        
        # Weights by severity
        weights = {
            FindingSeverity.CRITICAL: 25,
            FindingSeverity.HIGH: 15,
            FindingSeverity.MEDIUM: 8,
            FindingSeverity.LOW: 3,
            FindingSeverity.INFO: 0
        }
        
        penalty = sum(weights[f.severity] for f in self.universe.findings)
        
        # Cap at 0
        score = max(0, 100 - penalty)
        
        return round(score, 1)
