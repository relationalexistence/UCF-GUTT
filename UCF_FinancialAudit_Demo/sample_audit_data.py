"""
UCF/GUTT Audit Framework - Sample Data
======================================

Synthetic audit data for demonstration purposes.
Contains realistic scenarios with various control issues.

Copyright (c) 2026 Michael Fillippini. All Rights Reserved.
"""

from datetime import date, timedelta
from decimal import Decimal
import random

from audit_core import (
    AuditUniverse, Vendor, Customer, Employee, GLAccount,
    APTransaction, ARTransaction, PayrollTransaction, JournalEntry
)


def create_sample_company() -> AuditUniverse:
    """Create a sample company with realistic data and intentional issues."""
    
    universe = AuditUniverse("Acme Corporation - FY2025 Audit")
    
    # =========================================================================
    # EMPLOYEES
    # =========================================================================
    
    employees = [
        Employee(
            id="EMP001", name="John Smith", department="Finance", 
            title="CFO", is_management=True, authorization_limit=Decimal("100000"),
            hire_date=date(2020, 1, 15), address="123 Oak Street, Chicago, IL 60601",
            phone="312-555-1001", bank_account="****1234"
        ),
        Employee(
            id="EMP002", name="Sarah Johnson", department="Finance",
            title="Controller", is_management=True, authorization_limit=Decimal("50000"),
            hire_date=date(2019, 6, 1), address="456 Elm Ave, Chicago, IL 60602",
            phone="312-555-1002", bank_account="****2345"
        ),
        Employee(
            id="EMP003", name="Mike Brown", department="Finance",
            title="AP Manager", is_management=False, authorization_limit=Decimal("10000"),
            hire_date=date(2021, 3, 10), address="789 Pine Road, Chicago, IL 60603",
            phone="312-555-1003", bank_account="****3456"
        ),
        Employee(
            id="EMP004", name="Lisa Davis", department="Finance",
            title="AP Clerk", is_management=False, authorization_limit=Decimal("2500"),
            hire_date=date(2022, 8, 1), address="321 Maple Lane, Chicago, IL 60604",
            phone="312-555-1004", bank_account="****4567"
        ),
        Employee(
            id="EMP005", name="Tom Wilson", department="Operations",
            title="Purchasing Manager", is_management=False, authorization_limit=Decimal("25000"),
            hire_date=date(2020, 11, 15), address="654 Cedar Blvd, Chicago, IL 60605",
            phone="312-555-1005", bank_account="****5678"
        ),
        Employee(
            id="EMP006", name="Jennifer Lee", department="HR",
            title="HR Director", is_management=True, authorization_limit=Decimal("75000"),
            hire_date=date(2018, 4, 1), address="987 Birch Way, Chicago, IL 60606",
            phone="312-555-1006", bank_account="****6789"
        ),
        Employee(
            id="EMP007", name="David Martinez", department="Operations",
            title="Warehouse Worker", is_management=False, authorization_limit=Decimal("0"),
            hire_date=date(2023, 1, 15), hourly_rate=Decimal("22.50"),
            address="147 Spruce Court, Chicago, IL 60607",
            phone="312-555-1007", bank_account="****7890"
        ),
        Employee(
            id="EMP008", name="Emily Chen", department="Operations",
            title="Warehouse Supervisor", is_management=False, authorization_limit=Decimal("5000"),
            hire_date=date(2021, 9, 1), manager_id="EMP005", hourly_rate=Decimal("35.00"),
            address="258 Walnut Street, Chicago, IL 60608",
            phone="312-555-1008", bank_account="****8901"
        ),
        # Terminated employee (for testing)
        Employee(
            id="EMP009", name="Robert Taylor", department="Finance",
            title="Former Accountant", is_management=False,
            hire_date=date(2019, 1, 1), termination_date=date(2024, 6, 30),
            address="369 Ash Drive, Chicago, IL 60609",
            phone="312-555-1009", bank_account="****9012"
        ),
        # Employee with same address as a vendor (related party issue)
        Employee(
            id="EMP010", name="William Jones", department="Purchasing",
            title="Buyer", is_management=False, authorization_limit=Decimal("15000"),
            hire_date=date(2022, 2, 1),
            address="999 Suspicious Lane, Chicago, IL 60610",  # Same as vendor V007
            phone="312-555-1010", bank_account="****1111"
        ),
    ]
    
    for emp in employees:
        universe.add_employee(emp)
    
    # =========================================================================
    # VENDORS
    # =========================================================================
    
    vendors = [
        Vendor(
            id="V001", name="Office Supplies Inc",
            address="100 Commerce Drive, Chicago, IL 60611",
            phone="312-555-2001", tax_id="36-1234567",
            is_active=True, approved_date=date(2020, 1, 1), approved_by="EMP002",
            bank_account="****OSUP"
        ),
        Vendor(
            id="V002", name="Tech Solutions LLC",
            address="200 Innovation Way, Chicago, IL 60612",
            phone="312-555-2002", tax_id="36-2345678",
            is_active=True, approved_date=date(2020, 3, 15), approved_by="EMP002",
            bank_account="****TECH"
        ),
        Vendor(
            id="V003", name="Maintenance Services Co",
            address="300 Service Road, Chicago, IL 60613",
            phone="312-555-2003", tax_id="36-3456789",
            is_active=True, approved_date=date(2021, 6, 1), approved_by="EMP002",
            bank_account="****MAINT"
        ),
        Vendor(
            id="V004", name="Shipping Express",
            address="400 Logistics Ave, Chicago, IL 60614",
            phone="312-555-2004", tax_id="36-4567890",
            is_active=True, approved_date=date(2019, 8, 20), approved_by="EMP001",
            bank_account="****SHIP"
        ),
        # Inactive vendor (for testing payments to inactive vendors)
        Vendor(
            id="V005", name="Defunct Consulting",
            address="500 Closed Lane, Chicago, IL 60615",
            phone="312-555-2005", tax_id="36-5678901",
            is_active=False, approved_date=date(2018, 1, 1), approved_by="EMP001",
            bank_account="****DEAD"
        ),
        # Unapproved vendor
        Vendor(
            id="V006", name="Quick Supplies",
            address="600 Unapproved Blvd, Chicago, IL 60616",
            phone="312-555-2006", tax_id="36-6789012",
            is_active=True, approved_date=None, approved_by="",
            bank_account="****QSUP"
        ),
        # Vendor with same address as employee (related party issue)
        Vendor(
            id="V007", name="Jones Consulting",
            address="999 Suspicious Lane, Chicago, IL 60610",  # Same as EMP010
            phone="312-555-1010",  # Same phone as EMP010
            tax_id="36-7890123",
            is_active=True, approved_date=date(2023, 5, 1), approved_by="EMP003",
            bank_account="****JONE"
        ),
    ]
    
    for vendor in vendors:
        universe.add_vendor(vendor)
    
    # =========================================================================
    # CUSTOMERS
    # =========================================================================
    
    customers = [
        Customer(
            id="C001", name="Global Corp",
            address="1000 Enterprise Blvd, New York, NY 10001",
            phone="212-555-3001", credit_limit=Decimal("500000"),
            credit_approved_by="EMP001", is_active=True
        ),
        Customer(
            id="C002", name="Regional Industries",
            address="2000 Industrial Park, Detroit, MI 48201",
            phone="313-555-3002", credit_limit=Decimal("250000"),
            credit_approved_by="EMP002", is_active=True
        ),
        Customer(
            id="C003", name="Local Business LLC",
            address="3000 Main Street, Chicago, IL 60617",
            phone="312-555-3003", credit_limit=Decimal("50000"),
            credit_approved_by="EMP002", is_active=True
        ),
        Customer(
            id="C004", name="Slow Pay Company",
            address="4000 Delinquent Way, Los Angeles, CA 90001",
            phone="213-555-3004", credit_limit=Decimal("100000"),
            credit_approved_by="EMP002", is_active=True
        ),
    ]
    
    for customer in customers:
        universe.add_customer(customer)
    
    # =========================================================================
    # AP TRANSACTIONS (with various issues)
    # =========================================================================
    
    ap_transactions = [
        # Clean transaction - 3-way match, proper approvals
        APTransaction(
            id="AP001", vendor_id="V001",
            po_number="PO-2025-001", po_amount=Decimal("5000.00"),
            po_date=date(2025, 1, 5), po_created_by="EMP005", po_approved_by="EMP003",
            invoice_number="INV-OSI-1001", invoice_amount=Decimal("5000.00"),
            invoice_date=date(2025, 1, 10), invoice_received_by="EMP004",
            payment_amount=Decimal("5000.00"), payment_date=date(2025, 1, 25),
            payment_approved_by="EMP003", payment_processed_by="EMP004",
            gl_account="6100", description="Office supplies Q1"
        ),
        
        # Issue: Missing PO
        APTransaction(
            id="AP002", vendor_id="V002",
            po_number="", po_amount=Decimal("0"),  # No PO
            invoice_number="INV-TS-2001", invoice_amount=Decimal("15000.00"),
            invoice_date=date(2025, 1, 15), invoice_received_by="EMP004",
            payment_amount=Decimal("15000.00"), payment_date=date(2025, 1, 30),
            payment_approved_by="EMP002", payment_processed_by="EMP004",
            gl_account="6200", description="IT consulting services"
        ),
        
        # Issue: 3-way match failure
        APTransaction(
            id="AP003", vendor_id="V003",
            po_number="PO-2025-003", po_amount=Decimal("8000.00"),
            po_date=date(2025, 2, 1), po_created_by="EMP005", po_approved_by="EMP003",
            invoice_number="INV-MSC-3001", invoice_amount=Decimal("8500.00"),  # Different!
            invoice_date=date(2025, 2, 5), invoice_received_by="EMP004",
            payment_amount=Decimal("8500.00"), payment_date=date(2025, 2, 20),
            payment_approved_by="EMP003", payment_processed_by="EMP004",
            gl_account="6300", description="Maintenance services"
        ),
        
        # Issue: Segregation of duties - same person approved and processed
        APTransaction(
            id="AP004", vendor_id="V001",
            po_number="PO-2025-004", po_amount=Decimal("3000.00"),
            po_date=date(2025, 2, 10), po_created_by="EMP005", po_approved_by="EMP003",
            invoice_number="INV-OSI-1002", invoice_amount=Decimal("3000.00"),
            invoice_date=date(2025, 2, 15), invoice_received_by="EMP003",
            payment_amount=Decimal("3000.00"), payment_date=date(2025, 2, 28),
            payment_approved_by="EMP003", payment_processed_by="EMP003",  # Same person!
            gl_account="6100", description="Office supplies Feb"
        ),
        
        # Issue: Payment to inactive vendor
        APTransaction(
            id="AP005", vendor_id="V005",  # Inactive vendor!
            po_number="PO-2025-005", po_amount=Decimal("12000.00"),
            po_date=date(2025, 3, 1), po_created_by="EMP005", po_approved_by="EMP002",
            invoice_number="INV-DC-5001", invoice_amount=Decimal("12000.00"),
            invoice_date=date(2025, 3, 5), invoice_received_by="EMP004",
            payment_amount=Decimal("12000.00"), payment_date=date(2025, 3, 15),
            payment_approved_by="EMP002", payment_processed_by="EMP004",
            gl_account="6500", description="Legacy consulting closeout"
        ),
        
        # Issue: Authorization limit exceeded
        APTransaction(
            id="AP006", vendor_id="V002",
            po_number="PO-2025-006", po_amount=Decimal("75000.00"),
            po_date=date(2025, 3, 10), po_created_by="EMP005", po_approved_by="EMP002",
            invoice_number="INV-TS-2002", invoice_amount=Decimal("75000.00"),
            invoice_date=date(2025, 3, 15), invoice_received_by="EMP004",
            payment_amount=Decimal("75000.00"), payment_date=date(2025, 3, 30),
            payment_approved_by="EMP002",  # Limit is 50000!
            payment_processed_by="EMP004",
            gl_account="6200", description="Major IT upgrade"
        ),
        
        # Issue: Timing anomaly - invoice before PO
        APTransaction(
            id="AP007", vendor_id="V004",
            po_number="PO-2025-007", po_amount=Decimal("2500.00"),
            po_date=date(2025, 4, 15),  # PO after invoice!
            po_created_by="EMP005", po_approved_by="EMP003",
            invoice_number="INV-SE-4001", invoice_amount=Decimal("2500.00"),
            invoice_date=date(2025, 4, 1),  # Invoice before PO
            invoice_received_by="EMP004",
            payment_amount=Decimal("2500.00"), payment_date=date(2025, 4, 20),
            payment_approved_by="EMP003", payment_processed_by="EMP004",
            gl_account="6400", description="Shipping services"
        ),
        
        # Issue: Unapproved vendor
        APTransaction(
            id="AP008", vendor_id="V006",  # Unapproved vendor!
            po_number="PO-2025-008", po_amount=Decimal("1800.00"),
            po_date=date(2025, 4, 20), po_created_by="EMP005", po_approved_by="EMP003",
            invoice_number="INV-QS-6001", invoice_amount=Decimal("1800.00"),
            invoice_date=date(2025, 4, 22), invoice_received_by="EMP004",
            payment_amount=Decimal("1800.00"), payment_date=date(2025, 5, 5),
            payment_approved_by="EMP003", payment_processed_by="EMP004",
            gl_account="6100", description="Emergency supplies"
        ),
        
        # Issue: Related party vendor (V007 = employee EMP010)
        APTransaction(
            id="AP009", vendor_id="V007",  # Related party!
            po_number="PO-2025-009", po_amount=Decimal("25000.00"),
            po_date=date(2025, 5, 1), po_created_by="EMP010",  # Same employee!
            po_approved_by="EMP002",
            invoice_number="INV-JC-7001", invoice_amount=Decimal("25000.00"),
            invoice_date=date(2025, 5, 5), invoice_received_by="EMP004",
            payment_amount=Decimal("25000.00"), payment_date=date(2025, 5, 20),
            payment_approved_by="EMP002", payment_processed_by="EMP004",
            gl_account="6500", description="Consulting services"
        ),
        
        # Clean transaction
        APTransaction(
            id="AP010", vendor_id="V004",
            po_number="PO-2025-010", po_amount=Decimal("4200.00"),
            po_date=date(2025, 5, 10), po_created_by="EMP005", po_approved_by="EMP003",
            invoice_number="INV-SE-4002", invoice_amount=Decimal("4200.00"),
            invoice_date=date(2025, 5, 15), invoice_received_by="EMP004",
            payment_amount=Decimal("4200.00"), payment_date=date(2025, 5, 30),
            payment_approved_by="EMP003", payment_processed_by="EMP004",
            gl_account="6400", description="Monthly shipping"
        ),
    ]
    
    for txn in ap_transactions:
        universe.add_ap_transaction(txn)
    
    # =========================================================================
    # AR TRANSACTIONS
    # =========================================================================
    
    ar_transactions = [
        # Clean transaction
        ARTransaction(
            id="AR001", customer_id="C001",
            invoice_number="SI-2025-001", invoice_amount=Decimal("125000.00"),
            invoice_date=date(2025, 1, 15), invoice_created_by="EMP002",
            due_date=date(2025, 2, 14),
            payment_received=Decimal("125000.00"), payment_date=date(2025, 2, 10),
            gl_account="4100", description="Product sales Q1"
        ),
        
        # Issue: Unapproved write-off
        ARTransaction(
            id="AR002", customer_id="C004",
            invoice_number="SI-2025-002", invoice_amount=Decimal("35000.00"),
            invoice_date=date(2025, 1, 20), invoice_created_by="EMP002",
            due_date=date(2025, 2, 19),
            payment_received=Decimal("0"),
            write_off_amount=Decimal("35000.00"), write_off_approved_by="",  # No approval!
            gl_account="4100", description="Written off - no approval"
        ),
        
        # Issue: Severely aged receivable
        ARTransaction(
            id="AR003", customer_id="C004",
            invoice_number="SI-2024-050", invoice_amount=Decimal("48000.00"),
            invoice_date=date(2024, 9, 1),  # Very old!
            invoice_created_by="EMP002",
            due_date=date(2024, 10, 1),
            payment_received=Decimal("0"),
            gl_account="4100", description="Slow Pay Company - aging"
        ),
        
        # Issue: Credit limit exceeded
        ARTransaction(
            id="AR004", customer_id="C003",
            invoice_number="SI-2025-004", invoice_amount=Decimal("45000.00"),
            invoice_date=date(2025, 2, 1), invoice_created_by="EMP002",
            due_date=date(2025, 3, 2),
            payment_received=Decimal("0"),
            gl_account="4100", description="Local Business sale"
        ),
        ARTransaction(
            id="AR005", customer_id="C003",
            invoice_number="SI-2025-005", invoice_amount=Decimal("15000.00"),
            invoice_date=date(2025, 2, 15), invoice_created_by="EMP002",
            due_date=date(2025, 3, 16),
            payment_received=Decimal("0"),
            gl_account="4100", description="Additional sale - over limit"
        ),
        
        # Issue: Unapproved credit memo
        ARTransaction(
            id="AR006", customer_id="C002",
            invoice_number="SI-2025-006", invoice_amount=Decimal("80000.00"),
            invoice_date=date(2025, 3, 1), invoice_created_by="EMP002",
            due_date=date(2025, 3, 31),
            payment_received=Decimal("60000.00"), payment_date=date(2025, 3, 25),
            credit_memo_amount=Decimal("20000.00"), credit_memo_approved_by="",  # No approval!
            gl_account="4100", description="Partial credit given"
        ),
    ]
    
    for txn in ar_transactions:
        universe.add_ar_transaction(txn)
    
    # =========================================================================
    # PAYROLL TRANSACTIONS
    # =========================================================================
    
    payroll_transactions = [
        # Clean transaction
        PayrollTransaction(
            id="PAY001", employee_id="EMP007",
            pay_period_start=date(2025, 1, 1), pay_period_end=date(2025, 1, 15),
            regular_hours=Decimal("80"), overtime_hours=Decimal("0"),
            hourly_rate=Decimal("22.50"),
            gross_pay=Decimal("1800.00"), deductions=Decimal("450.00"),
            net_pay=Decimal("1350.00"),
            timesheet_approved_by="EMP008", payroll_processed_by="EMP004",
            has_timesheet=True, payment_date=date(2025, 1, 20),
            gl_account="5100"
        ),
        
        # Issue: Missing timesheet
        PayrollTransaction(
            id="PAY002", employee_id="EMP007",
            pay_period_start=date(2025, 1, 16), pay_period_end=date(2025, 1, 31),
            regular_hours=Decimal("80"), overtime_hours=Decimal("10"),
            hourly_rate=Decimal("22.50"),
            gross_pay=Decimal("2137.50"), deductions=Decimal("534.38"),
            net_pay=Decimal("1603.12"),
            timesheet_approved_by="EMP008", payroll_processed_by="EMP004",
            has_timesheet=False,  # Missing!
            payment_date=date(2025, 2, 5),
            gl_account="5100"
        ),
        
        # Issue: Unapproved overtime
        PayrollTransaction(
            id="PAY003", employee_id="EMP008",
            pay_period_start=date(2025, 2, 1), pay_period_end=date(2025, 2, 15),
            regular_hours=Decimal("80"), overtime_hours=Decimal("20"),
            hourly_rate=Decimal("35.00"),
            gross_pay=Decimal("3850.00"), deductions=Decimal("962.50"),
            net_pay=Decimal("2887.50"),
            timesheet_approved_by="",  # No approval for OT!
            payroll_processed_by="EMP004",
            has_timesheet=True, payment_date=date(2025, 2, 20),
            gl_account="5100"
        ),
        
        # Issue: Payment to terminated employee
        PayrollTransaction(
            id="PAY004", employee_id="EMP009",  # Terminated!
            pay_period_start=date(2025, 1, 1), pay_period_end=date(2025, 1, 15),
            regular_hours=Decimal("80"), overtime_hours=Decimal("0"),
            hourly_rate=Decimal("30.00"),
            gross_pay=Decimal("2400.00"), deductions=Decimal("600.00"),
            net_pay=Decimal("1800.00"),
            timesheet_approved_by="EMP002", payroll_processed_by="EMP004",
            has_timesheet=True, payment_date=date(2025, 1, 20),
            gl_account="5100"
        ),
        
        # Issue: Ghost employee (unknown ID)
        PayrollTransaction(
            id="PAY005", employee_id="EMP999",  # Doesn't exist!
            pay_period_start=date(2025, 2, 1), pay_period_end=date(2025, 2, 15),
            regular_hours=Decimal("80"), overtime_hours=Decimal("0"),
            hourly_rate=Decimal("25.00"),
            gross_pay=Decimal("2000.00"), deductions=Decimal("500.00"),
            net_pay=Decimal("1500.00"),
            timesheet_approved_by="EMP005", payroll_processed_by="EMP004",
            has_timesheet=True, payment_date=date(2025, 2, 20),
            gl_account="5100"
        ),
        
        # Issue: Self-approved timesheet
        PayrollTransaction(
            id="PAY006", employee_id="EMP005",
            pay_period_start=date(2025, 2, 16), pay_period_end=date(2025, 2, 28),
            regular_hours=Decimal("80"), overtime_hours=Decimal("15"),
            hourly_rate=Decimal("45.00"),
            gross_pay=Decimal("4612.50"), deductions=Decimal("1153.13"),
            net_pay=Decimal("3459.37"),
            timesheet_approved_by="EMP005",  # Self-approved!
            payroll_processed_by="EMP004",
            has_timesheet=True, payment_date=date(2025, 3, 5),
            gl_account="5100"
        ),
        
        # Issue: Gross pay calculation error
        PayrollTransaction(
            id="PAY007", employee_id="EMP007",
            pay_period_start=date(2025, 3, 1), pay_period_end=date(2025, 3, 15),
            regular_hours=Decimal("80"), overtime_hours=Decimal("5"),
            hourly_rate=Decimal("22.50"),
            gross_pay=Decimal("2100.00"),  # Should be 80*22.50 + 5*22.50*1.5 = 1800 + 168.75 = 1968.75
            deductions=Decimal("525.00"),
            net_pay=Decimal("1575.00"),
            timesheet_approved_by="EMP008", payroll_processed_by="EMP004",
            has_timesheet=True, payment_date=date(2025, 3, 20),
            gl_account="5100"
        ),
    ]
    
    for txn in payroll_transactions:
        universe.add_payroll_transaction(txn)
    
    # =========================================================================
    # JOURNAL ENTRIES
    # =========================================================================
    
    journal_entries = [
        # Clean entry
        JournalEntry(
            id="JE001",
            entry_date=date(2025, 1, 31), posting_date=date(2025, 1, 31),
            description="Monthly depreciation expense - January 2025",
            lines=[
                {'account': '6600', 'debit': Decimal('15000'), 'credit': Decimal('0')},
                {'account': '1500', 'debit': Decimal('0'), 'credit': Decimal('15000')},
            ],
            created_by="EMP002", approved_by="EMP001",
            is_manual=True, source_system="Manual"
        ),
        
        # Issue: Unbalanced entry
        JournalEntry(
            id="JE002",
            entry_date=date(2025, 2, 28), posting_date=date(2025, 2, 28),
            description="Accrued expenses",
            lines=[
                {'account': '6700', 'debit': Decimal('25000'), 'credit': Decimal('0')},
                {'account': '2100', 'debit': Decimal('0'), 'credit': Decimal('24000')},  # Doesn't balance!
            ],
            created_by="EMP002", approved_by="EMP001",
            is_manual=True, source_system="Manual"
        ),
        
        # Issue: Unapproved manual entry
        JournalEntry(
            id="JE003",
            entry_date=date(2025, 3, 15), posting_date=date(2025, 3, 15),
            description="Misc adjustment",
            lines=[
                {'account': '6800', 'debit': Decimal('8000'), 'credit': Decimal('0')},
                {'account': '1100', 'debit': Decimal('0'), 'credit': Decimal('8000')},
            ],
            created_by="EMP003", approved_by="",  # No approval!
            is_manual=True, source_system="Manual"
        ),
        
        # Issue: Self-approved entry
        JournalEntry(
            id="JE004",
            entry_date=date(2025, 3, 31), posting_date=date(2025, 3, 31),
            description="Quarter-end accrual",
            lines=[
                {'account': '6900', 'debit': Decimal('12000'), 'credit': Decimal('0')},
                {'account': '2200', 'debit': Decimal('0'), 'credit': Decimal('12000')},
            ],
            created_by="EMP002", approved_by="EMP002",  # Self-approved!
            is_manual=True, source_system="Manual"
        ),
        
        # Issue: Round amount (fraud indicator)
        JournalEntry(
            id="JE005",
            entry_date=date(2025, 4, 15), posting_date=date(2025, 4, 15),
            description="Adjustment",
            lines=[
                {'account': '6100', 'debit': Decimal('50000'), 'credit': Decimal('0')},  # Round!
                {'account': '1100', 'debit': Decimal('0'), 'credit': Decimal('50000')},
            ],
            created_by="EMP003", approved_by="EMP002",
            is_manual=True, source_system="Manual"
        ),
        
        # Issue: Insufficient description
        JournalEntry(
            id="JE006",
            entry_date=date(2025, 4, 30), posting_date=date(2025, 4, 30),
            description="Adj",  # Too short!
            lines=[
                {'account': '6200', 'debit': Decimal('3500'), 'credit': Decimal('0')},
                {'account': '2100', 'debit': Decimal('0'), 'credit': Decimal('3500')},
            ],
            created_by="EMP002", approved_by="EMP001",
            is_manual=True, source_system="Manual"
        ),
        
        # Clean automated entry
        JournalEntry(
            id="JE007",
            entry_date=date(2025, 5, 31), posting_date=date(2025, 5, 31),
            description="Monthly payroll posting from ADP - May 2025",
            lines=[
                {'account': '5100', 'debit': Decimal('125000'), 'credit': Decimal('0')},
                {'account': '2300', 'debit': Decimal('0'), 'credit': Decimal('31250')},
                {'account': '1000', 'debit': Decimal('0'), 'credit': Decimal('93750')},
            ],
            created_by="SYSTEM", approved_by="",
            is_manual=False, source_system="Payroll"
        ),
    ]
    
    for entry in journal_entries:
        universe.add_journal_entry(entry)
    
    return universe


def create_clean_company() -> AuditUniverse:
    """Create a sample company with mostly clean data (for comparison)."""
    
    universe = AuditUniverse("Best Practices Corp - FY2025 Audit")
    
    # Add basic employees
    employees = [
        Employee(
            id="EMP001", name="CEO", department="Executive",
            title="CEO", is_management=True, authorization_limit=Decimal("1000000"),
            hire_date=date(2015, 1, 1)
        ),
        Employee(
            id="EMP002", name="CFO", department="Finance",
            title="CFO", is_management=True, authorization_limit=Decimal("500000"),
            hire_date=date(2016, 1, 1)
        ),
        Employee(
            id="EMP003", name="AP Manager", department="Finance",
            title="AP Manager", is_management=False, authorization_limit=Decimal("50000"),
            hire_date=date(2018, 1, 1)
        ),
        Employee(
            id="EMP004", name="AP Clerk", department="Finance",
            title="AP Clerk", is_management=False, authorization_limit=Decimal("5000"),
            hire_date=date(2020, 1, 1)
        ),
    ]
    
    for emp in employees:
        universe.add_employee(emp)
    
    # Add approved vendor
    vendor = Vendor(
        id="V001", name="Approved Vendor Inc",
        address="100 Legitimate Street",
        is_active=True, approved_date=date(2020, 1, 1), approved_by="EMP002"
    )
    universe.add_vendor(vendor)
    
    # Add clean AP transaction
    txn = APTransaction(
        id="AP001", vendor_id="V001",
        po_number="PO-001", po_amount=Decimal("10000"),
        po_date=date(2025, 1, 1), po_created_by="EMP004", po_approved_by="EMP003",
        invoice_number="INV-001", invoice_amount=Decimal("10000"),
        invoice_date=date(2025, 1, 5), invoice_received_by="EMP004",
        payment_amount=Decimal("10000"), payment_date=date(2025, 1, 20),
        payment_approved_by="EMP003", payment_processed_by="EMP004"
    )
    universe.add_ap_transaction(txn)
    
    return universe
