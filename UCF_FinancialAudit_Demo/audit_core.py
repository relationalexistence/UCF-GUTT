"""
UCF/GUTT Audit Framework - Core Module
======================================

DEMONSTRATION VERSION - Simplified algorithms for concept illustration.
Production system uses proprietary UCF/GUTT tensor analysis.

Copyright (c) 2026 Michael Fillippini. All Rights Reserved.

Relational Audit Theory:
- Entities: Transactions, Accounts, Vendors, Customers, Employees, Documents
- Relations: Multi-channel connections between entities
- R_conflict: Inconsistencies that indicate control failures or fraud
- R_harmony: Consistent patterns indicating clean transactions

SOX Compliance:
- Segregation of duties
- Authorization controls
- Documentation requirements
- Management review
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple, Any
from enum import Enum
from datetime import datetime, date
from decimal import Decimal
import hashlib

__version__ = "DEMO-1.0"
__author__ = "Michael Fillippini"
__copyright__ = "Copyright (c) 2026 Michael Fillippini. All Rights Reserved."


# =============================================================================
# ENUMS - Transaction Types and Channels
# =============================================================================

class TransactionDomain(Enum):
    """Major audit domains."""
    AP = "accounts_payable"
    AR = "accounts_receivable"
    PAYROLL = "payroll"
    GL = "general_ledger"


class APChannel(Enum):
    """Accounts Payable relationship channels."""
    DOCUMENTATION = "documentation"      # PO, invoice, receipt exist and match
    AUTHORIZATION = "authorization"      # Proper approval chain followed
    TIMING = "timing"                    # Correct sequence (PO→Invoice→Payment)
    AMOUNT = "amount"                    # 3-way match (PO, invoice, payment)
    COUNTERPARTY = "counterparty"        # Vendor legitimacy
    SEGREGATION = "segregation"          # Different people for different steps


class ARChannel(Enum):
    """Accounts Receivable relationship channels."""
    DOCUMENTATION = "documentation"      # Invoice, contract exist
    AUTHORIZATION = "authorization"      # Credit approval, write-off approval
    TIMING = "timing"                    # Aging, collection sequence
    AMOUNT = "amount"                    # Invoice vs receipt vs credit memo
    CUSTOMER = "customer"                # Customer legitimacy
    SEGREGATION = "segregation"          # Separation of duties


class PayrollChannel(Enum):
    """Payroll relationship channels."""
    DOCUMENTATION = "documentation"      # Timesheet, contract, tax forms
    AUTHORIZATION = "authorization"      # Manager approval, HR verification
    TIMING = "timing"                    # Pay period alignment
    AMOUNT = "amount"                    # Rate × hours = pay, deductions
    EMPLOYEE = "employee"                # Employee exists, active, valid bank
    SEGREGATION = "segregation"          # HR vs Payroll vs Approver


class GLChannel(Enum):
    """General Ledger relationship channels."""
    DOCUMENTATION = "documentation"      # Support for journal entry
    AUTHORIZATION = "authorization"      # Approval for manual entries
    TIMING = "timing"                    # Period-appropriate posting
    AMOUNT = "amount"                    # Reasonableness, round numbers
    BALANCE = "balance"                  # Debits = Credits
    SEGREGATION = "segregation"          # Preparer vs reviewer


class SOXControl(Enum):
    """SOX control categories."""
    SEGREGATION = "segregation_of_duties"
    AUTHORIZATION = "authorization_limits"
    MANAGEMENT_REVIEW = "management_review"
    RECONCILIATION = "reconciliation"
    ACCESS_CONTROL = "access_control"
    DOCUMENTATION = "documentation"


class FindingSeverity(Enum):
    """Audit finding severity levels."""
    CRITICAL = "critical"      # Material misstatement risk, fraud indicator
    HIGH = "high"              # Significant control deficiency
    MEDIUM = "medium"          # Control weakness
    LOW = "low"                # Minor issue, best practice
    INFO = "informational"     # Observation only


class RelatedPartyType(Enum):
    """Types of related party relationships."""
    EMPLOYEE_VENDOR = "employee_vendor"
    EMPLOYEE_CUSTOMER = "employee_customer"
    MANAGEMENT_VENDOR = "management_vendor"
    VENDOR_CUSTOMER = "vendor_customer"
    ADDRESS_MATCH = "address_match"
    BANK_MATCH = "bank_account_match"
    PHONE_MATCH = "phone_match"


# =============================================================================
# DATA CLASSES - Entities
# =============================================================================

@dataclass
class Entity:
    """Base class for all audit entities."""
    id: str
    name: str
    entity_type: str = ""
    created_date: date = field(default_factory=date.today)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def fingerprint(self) -> str:
        """Generate a fingerprint for matching."""
        # Normalize for comparison
        normalized = f"{self.name.lower().strip()}"
        return hashlib.md5(normalized.encode()).hexdigest()[:8]


@dataclass
class Vendor(Entity):
    """Vendor/Supplier entity."""
    address: str = ""
    phone: str = ""
    bank_account: str = ""
    tax_id: str = ""
    is_active: bool = True
    approved_date: Optional[date] = None
    approved_by: str = ""
    
    def __post_init__(self):
        self.entity_type = "vendor"


@dataclass
class Customer(Entity):
    """Customer entity."""
    address: str = ""
    phone: str = ""
    credit_limit: Decimal = Decimal("0")
    credit_approved_by: str = ""
    is_active: bool = True
    
    def __post_init__(self):
        self.entity_type = "customer"


@dataclass
class Employee(Entity):
    """Employee entity."""
    department: str = ""
    title: str = ""
    manager_id: str = ""
    hire_date: Optional[date] = None
    termination_date: Optional[date] = None
    address: str = ""
    phone: str = ""
    bank_account: str = ""
    hourly_rate: Decimal = Decimal("0")
    salary: Decimal = Decimal("0")
    is_management: bool = False
    authorization_limit: Decimal = Decimal("0")
    
    def __post_init__(self):
        self.entity_type = "employee"
    
    def is_active(self, as_of: date = None) -> bool:
        as_of = as_of or date.today()
        if self.termination_date and self.termination_date <= as_of:
            return False
        if self.hire_date and self.hire_date > as_of:
            return False
        return True


@dataclass
class GLAccount(Entity):
    """General Ledger account."""
    account_number: str = ""
    account_type: str = ""  # asset, liability, equity, revenue, expense
    normal_balance: str = "debit"  # debit or credit
    is_active: bool = True
    
    def __post_init__(self):
        self.entity_type = "gl_account"


@dataclass 
class Document:
    """Supporting document."""
    id: str
    doc_type: str  # PO, invoice, receipt, contract, timesheet, etc.
    reference_number: str
    date: date
    amount: Decimal
    related_entity_id: str  # vendor, customer, employee
    created_by: str
    approved_by: str = ""
    approved_date: Optional[date] = None
    metadata: Dict[str, Any] = field(default_factory=dict)


# =============================================================================
# DATA CLASSES - Transactions
# =============================================================================

@dataclass
class APTransaction:
    """Accounts Payable transaction."""
    id: str
    vendor_id: str
    po_number: str = ""
    po_amount: Decimal = Decimal("0")
    po_date: Optional[date] = None
    po_created_by: str = ""
    po_approved_by: str = ""
    
    invoice_number: str = ""
    invoice_amount: Decimal = Decimal("0")
    invoice_date: Optional[date] = None
    invoice_received_by: str = ""
    
    payment_amount: Decimal = Decimal("0")
    payment_date: Optional[date] = None
    payment_approved_by: str = ""
    payment_processed_by: str = ""
    
    gl_account: str = ""
    description: str = ""
    
    def three_way_match(self) -> Tuple[bool, str]:
        """Check if PO, invoice, and payment amounts match."""
        if self.po_amount == Decimal("0"):
            return False, "Missing PO amount"
        if self.invoice_amount == Decimal("0"):
            return False, "Missing invoice amount"
        if self.payment_amount == Decimal("0"):
            return False, "Missing payment amount"
        
        if self.po_amount != self.invoice_amount:
            diff = abs(self.po_amount - self.invoice_amount)
            return False, f"PO ({self.po_amount}) ≠ Invoice ({self.invoice_amount}), diff: {diff}"
        
        if self.invoice_amount != self.payment_amount:
            diff = abs(self.invoice_amount - self.payment_amount)
            return False, f"Invoice ({self.invoice_amount}) ≠ Payment ({self.payment_amount}), diff: {diff}"
        
        return True, "3-way match OK"


@dataclass
class ARTransaction:
    """Accounts Receivable transaction."""
    id: str
    customer_id: str
    invoice_number: str
    invoice_amount: Decimal
    invoice_date: date
    invoice_created_by: str
    
    due_date: date = None
    payment_received: Decimal = Decimal("0")
    payment_date: Optional[date] = None
    
    credit_memo_amount: Decimal = Decimal("0")
    credit_memo_approved_by: str = ""
    
    write_off_amount: Decimal = Decimal("0")
    write_off_approved_by: str = ""
    
    gl_account: str = ""
    description: str = ""
    
    def balance_due(self) -> Decimal:
        return self.invoice_amount - self.payment_received - self.credit_memo_amount - self.write_off_amount
    
    def days_outstanding(self, as_of: date = None) -> int:
        as_of = as_of or date.today()
        if self.payment_date:
            return 0
        return (as_of - self.invoice_date).days


@dataclass
class PayrollTransaction:
    """Payroll transaction."""
    id: str
    employee_id: str
    pay_period_start: date
    pay_period_end: date
    
    regular_hours: Decimal = Decimal("0")
    overtime_hours: Decimal = Decimal("0")
    hourly_rate: Decimal = Decimal("0")
    
    gross_pay: Decimal = Decimal("0")
    deductions: Decimal = Decimal("0")
    net_pay: Decimal = Decimal("0")
    
    timesheet_approved_by: str = ""
    payroll_processed_by: str = ""
    payment_date: Optional[date] = None
    
    has_timesheet: bool = False
    gl_account: str = ""
    
    def calculated_gross(self) -> Decimal:
        """Calculate expected gross pay."""
        regular = self.regular_hours * self.hourly_rate
        overtime = self.overtime_hours * self.hourly_rate * Decimal("1.5")
        return regular + overtime
    
    def gross_variance(self) -> Decimal:
        """Variance between calculated and recorded gross."""
        return abs(self.gross_pay - self.calculated_gross())


@dataclass
class JournalEntry:
    """General Ledger journal entry."""
    id: str
    entry_date: date
    posting_date: date
    description: str
    
    lines: List[Dict] = field(default_factory=list)  # [{account, debit, credit}]
    
    created_by: str = ""
    approved_by: str = ""
    is_manual: bool = False
    is_reversing: bool = False
    reversed_entry_id: str = ""
    
    source_system: str = ""  # AP, AR, Payroll, Manual
    
    def total_debits(self) -> Decimal:
        return sum(Decimal(str(line.get('debit', 0))) for line in self.lines)
    
    def total_credits(self) -> Decimal:
        return sum(Decimal(str(line.get('credit', 0))) for line in self.lines)
    
    def is_balanced(self) -> bool:
        return self.total_debits() == self.total_credits()
    
    def is_round_amount(self) -> bool:
        """Check if amounts are suspiciously round."""
        for line in self.lines:
            debit = Decimal(str(line.get('debit', 0)))
            credit = Decimal(str(line.get('credit', 0)))
            for amt in [debit, credit]:
                if amt > 0 and amt % 1000 == 0 and amt >= 10000:
                    return True
        return False


# =============================================================================
# RELATIONAL TENSOR - Multi-channel relationship weights
# =============================================================================

class AuditRelationalTensor:
    """
    DEMO: Simplified relational tensor for audit analysis.
    
    Production version uses full NRT (Nested Relational Tensor) with:
    - Coq-verified predicates
    - Temporal evolution tracking
    - Cascade effect modeling
    """
    
    def __init__(self, domain: TransactionDomain):
        self.domain = domain
        self._weights: Dict[str, Dict[str, Dict[str, float]]] = {}
        # Structure: {channel: {source_id: {target_id: weight}}}
        
        # Get channels for this domain
        if domain == TransactionDomain.AP:
            self._channels = [c.value for c in APChannel]
        elif domain == TransactionDomain.AR:
            self._channels = [c.value for c in ARChannel]
        elif domain == TransactionDomain.PAYROLL:
            self._channels = [c.value for c in PayrollChannel]
        else:
            self._channels = [c.value for c in GLChannel]
        
        # Initialize channel dictionaries
        for ch in self._channels:
            self._weights[ch] = {}
    
    def set_weight(self, channel: str, source: str, target: str, weight: float):
        """Set relationship weight. Weight: -1 (violation) to +1 (compliant)."""
        if channel not in self._weights:
            return
        if source not in self._weights[channel]:
            self._weights[channel][source] = {}
        self._weights[channel][source][target] = max(-1.0, min(1.0, weight))
    
    def get_weight(self, channel: str, source: str, target: str) -> float:
        """Get relationship weight."""
        return self._weights.get(channel, {}).get(source, {}).get(target, 0.0)
    
    def get_all_channels(self, source: str, target: str) -> Dict[str, float]:
        """Get all channel weights for a relationship."""
        return {ch: self.get_weight(ch, source, target) for ch in self._channels}
    
    def has_conflict(self, source: str, target: str) -> bool:
        """
        DEMO: Basic conflict detection.
        R_conflict = at least one positive AND at least one negative channel.
        
        In audit context: positive = compliant, negative = violation
        Conflict means mixed signals - some controls pass, some fail.
        """
        channels = self.get_all_channels(source, target)
        has_positive = any(w > 0 for w in channels.values())
        has_negative = any(w < 0 for w in channels.values())
        return has_positive and has_negative
    
    def has_control_failure(self, source: str, target: str) -> bool:
        """Any negative channel = control failure."""
        channels = self.get_all_channels(source, target)
        return any(w < 0 for w in channels.values())
    
    def is_clean(self, source: str, target: str) -> bool:
        """All channels positive or zero = clean transaction."""
        channels = self.get_all_channels(source, target)
        return all(w >= 0 for w in channels.values()) and any(w > 0 for w in channels.values())
    
    def control_score(self, source: str, target: str) -> float:
        """
        DEMO: Simple control compliance score.
        Production uses calibrated multi-factor analysis.
        """
        channels = self.get_all_channels(source, target)
        active = [w for w in channels.values() if w != 0]
        if not active:
            return 0.0
        return sum(active) / len(active)
    
    def get_violations(self, source: str, target: str) -> List[Tuple[str, float]]:
        """Get list of violated channels (negative weights)."""
        channels = self.get_all_channels(source, target)
        return [(ch, w) for ch, w in channels.items() if w < 0]


# =============================================================================
# AUDIT FINDING
# =============================================================================

@dataclass
class AuditFinding:
    """Audit finding/exception."""
    id: str
    domain: TransactionDomain
    severity: FindingSeverity
    sox_control: Optional[SOXControl]
    
    title: str
    description: str
    
    entity_ids: List[str] = field(default_factory=list)
    transaction_ids: List[str] = field(default_factory=list)
    
    channel_violations: Dict[str, float] = field(default_factory=dict)
    
    recommendation: str = ""
    
    detected_date: date = field(default_factory=date.today)
    
    def to_dict(self) -> Dict:
        return {
            'id': self.id,
            'domain': self.domain.value,
            'severity': self.severity.value,
            'sox_control': self.sox_control.value if self.sox_control else None,
            'title': self.title,
            'description': self.description,
            'entity_ids': self.entity_ids,
            'transaction_ids': self.transaction_ids,
            'channel_violations': self.channel_violations,
            'recommendation': self.recommendation,
        }


# =============================================================================
# RELATED PARTY DETECTION
# =============================================================================

class RelatedPartyDetector:
    """
    DEMO: Basic related party detection.
    Production uses advanced matching algorithms and network analysis.
    """
    
    def __init__(self):
        self.matches: List[Dict] = []
    
    def check_employee_vendor(self, employee: Employee, vendor: Vendor) -> List[Dict]:
        """Check for employee-vendor relationships."""
        findings = []
        
        # Name similarity (basic)
        emp_name = employee.name.lower().strip()
        vendor_name = vendor.name.lower().strip()
        if emp_name in vendor_name or vendor_name in emp_name:
            findings.append({
                'type': RelatedPartyType.EMPLOYEE_VENDOR,
                'match_reason': 'name_similarity',
                'employee_id': employee.id,
                'vendor_id': vendor.id,
                'details': f"Name match: {employee.name} ~ {vendor.name}",
                'severity': FindingSeverity.HIGH
            })
        
        # Address match
        if employee.address and vendor.address:
            emp_addr = employee.address.lower().strip()
            vendor_addr = vendor.address.lower().strip()
            if emp_addr == vendor_addr:
                findings.append({
                    'type': RelatedPartyType.ADDRESS_MATCH,
                    'match_reason': 'same_address',
                    'employee_id': employee.id,
                    'vendor_id': vendor.id,
                    'details': f"Same address: {employee.address}",
                    'severity': FindingSeverity.CRITICAL
                })
        
        # Bank account match
        if employee.bank_account and vendor.bank_account:
            if employee.bank_account == vendor.bank_account:
                findings.append({
                    'type': RelatedPartyType.BANK_MATCH,
                    'match_reason': 'same_bank_account',
                    'employee_id': employee.id,
                    'vendor_id': vendor.id,
                    'details': f"Same bank account: ****{employee.bank_account[-4:]}",
                    'severity': FindingSeverity.CRITICAL
                })
        
        # Phone match
        if employee.phone and vendor.phone:
            emp_phone = ''.join(filter(str.isdigit, employee.phone))
            vendor_phone = ''.join(filter(str.isdigit, vendor.phone))
            if emp_phone == vendor_phone and emp_phone:
                findings.append({
                    'type': RelatedPartyType.PHONE_MATCH,
                    'match_reason': 'same_phone',
                    'employee_id': employee.id,
                    'vendor_id': vendor.id,
                    'details': f"Same phone: {employee.phone}",
                    'severity': FindingSeverity.HIGH
                })
        
        return findings
    
    def check_management_vendor(self, employee: Employee, vendor: Vendor) -> List[Dict]:
        """Check for management-vendor relationships (heightened scrutiny)."""
        if not employee.is_management:
            return []
        
        findings = self.check_employee_vendor(employee, vendor)
        
        # Upgrade severity for management
        for f in findings:
            if f['severity'] == FindingSeverity.HIGH:
                f['severity'] = FindingSeverity.CRITICAL
            f['details'] += " [MANAGEMENT]"
        
        return findings
    
    def detect_all(self, employees: List[Employee], vendors: List[Vendor], 
                   customers: List[Customer] = None) -> List[Dict]:
        """Run all related party checks."""
        findings = []
        
        for emp in employees:
            for vendor in vendors:
                if emp.is_management:
                    findings.extend(self.check_management_vendor(emp, vendor))
                else:
                    findings.extend(self.check_employee_vendor(emp, vendor))
        
        # Could add customer checks here
        
        self.matches = findings
        return findings


# =============================================================================
# AUDIT UNIVERSE - Container for all entities and transactions
# =============================================================================

class AuditUniverse:
    """
    Container for all audit entities, transactions, and relationships.
    Provides methods for analysis and finding generation.
    """
    
    def __init__(self, name: str = "Audit Universe"):
        self.name = name
        
        # Entities
        self.vendors: Dict[str, Vendor] = {}
        self.customers: Dict[str, Customer] = {}
        self.employees: Dict[str, Employee] = {}
        self.gl_accounts: Dict[str, GLAccount] = {}
        self.documents: Dict[str, Document] = {}
        
        # Transactions
        self.ap_transactions: Dict[str, APTransaction] = {}
        self.ar_transactions: Dict[str, ARTransaction] = {}
        self.payroll_transactions: Dict[str, PayrollTransaction] = {}
        self.journal_entries: Dict[str, JournalEntry] = {}
        
        # Relational tensors for each domain
        self.ap_tensor = AuditRelationalTensor(TransactionDomain.AP)
        self.ar_tensor = AuditRelationalTensor(TransactionDomain.AR)
        self.payroll_tensor = AuditRelationalTensor(TransactionDomain.PAYROLL)
        self.gl_tensor = AuditRelationalTensor(TransactionDomain.GL)
        
        # Findings
        self.findings: List[AuditFinding] = []
        
        # Related party detector
        self.related_party_detector = RelatedPartyDetector()
    
    # --- Add entities ---
    
    def add_vendor(self, vendor: Vendor):
        self.vendors[vendor.id] = vendor
    
    def add_customer(self, customer: Customer):
        self.customers[customer.id] = customer
    
    def add_employee(self, employee: Employee):
        self.employees[employee.id] = employee
    
    def add_gl_account(self, account: GLAccount):
        self.gl_accounts[account.id] = account
    
    # --- Add transactions ---
    
    def add_ap_transaction(self, txn: APTransaction):
        self.ap_transactions[txn.id] = txn
    
    def add_ar_transaction(self, txn: ARTransaction):
        self.ar_transactions[txn.id] = txn
    
    def add_payroll_transaction(self, txn: PayrollTransaction):
        self.payroll_transactions[txn.id] = txn
    
    def add_journal_entry(self, entry: JournalEntry):
        self.journal_entries[entry.id] = entry
    
    # --- Statistics ---
    
    def stats(self) -> Dict[str, int]:
        return {
            'vendors': len(self.vendors),
            'customers': len(self.customers),
            'employees': len(self.employees),
            'gl_accounts': len(self.gl_accounts),
            'ap_transactions': len(self.ap_transactions),
            'ar_transactions': len(self.ar_transactions),
            'payroll_transactions': len(self.payroll_transactions),
            'journal_entries': len(self.journal_entries),
            'findings': len(self.findings),
        }
    
    def get_tensor(self, domain: TransactionDomain) -> AuditRelationalTensor:
        """Get the relational tensor for a domain."""
        if domain == TransactionDomain.AP:
            return self.ap_tensor
        elif domain == TransactionDomain.AR:
            return self.ar_tensor
        elif domain == TransactionDomain.PAYROLL:
            return self.payroll_tensor
        else:
            return self.gl_tensor
