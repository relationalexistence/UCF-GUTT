"""
Sample Datasets for UCF/GUTT Demo
==================================

Provides diverse team configurations for demonstration purposes.

Copyright (C) 2023-2026 Michael Fillippini. All Rights Reserved.
"""

from org_analysis import (
    OrganizationalNetwork,
    TeamMember,
    RelationshipChannel
)


def create_startup_team() -> OrganizationalNetwork:
    """
    Create a startup team with typical founder dynamics.
    
    Scenario: Early-stage startup with co-founders who have
    strong collaboration but some trust tensions.
    """
    network = OrganizationalNetwork("Startup Founding Team")
    
    members = [
        TeamMember("ceo", "Jordan Lee", "CEO/Co-founder", "Executive"),
        TeamMember("cto", "Alex Rivera", "CTO/Co-founder", "Engineering"),
        TeamMember("cfo", "Sam Chen", "CFO", "Finance"),
        TeamMember("dev1", "Morgan Park", "Lead Developer", "Engineering"),
        TeamMember("design", "Casey Taylor", "Head of Design", "Product"),
    ]
    
    for m in members:
        network.add_member(m)
    
    # CEO <-> CTO: Strong partnership with some tension on priorities
    network.set_relationship("ceo", "cto", RelationshipChannel.COLLABORATION, 0.9)
    network.set_relationship("ceo", "cto", RelationshipChannel.TRUST, 0.7)
    network.set_relationship("ceo", "cto", RelationshipChannel.COMMUNICATION, 0.8)
    network.set_relationship("ceo", "cto", RelationshipChannel.INFLUENCE, 0.6)
    
    network.set_relationship("cto", "ceo", RelationshipChannel.COLLABORATION, 0.85)
    network.set_relationship("cto", "ceo", RelationshipChannel.TRUST, 0.6)  # Slight trust concern
    network.set_relationship("cto", "ceo", RelationshipChannel.COMMUNICATION, 0.7)
    network.set_relationship("cto", "ceo", RelationshipChannel.INFLUENCE, -0.2)  # Feels overridden sometimes
    
    # CEO <-> CFO: Professional but cool
    network.set_relationship("ceo", "cfo", RelationshipChannel.COLLABORATION, 0.6)
    network.set_relationship("ceo", "cfo", RelationshipChannel.TRUST, 0.8)
    network.set_relationship("ceo", "cfo", RelationshipChannel.COMMUNICATION, 0.5)
    
    network.set_relationship("cfo", "ceo", RelationshipChannel.TRUST, 0.9)
    network.set_relationship("cfo", "ceo", RelationshipChannel.REPORTING, 0.8)
    
    # CTO <-> Lead Dev: Technical mentorship
    network.set_relationship("cto", "dev1", RelationshipChannel.COLLABORATION, 0.8)
    network.set_relationship("cto", "dev1", RelationshipChannel.TRUST, 0.85)
    network.set_relationship("cto", "dev1", RelationshipChannel.INFLUENCE, 0.7)
    network.set_relationship("cto", "dev1", RelationshipChannel.SOCIAL, 0.6)
    
    network.set_relationship("dev1", "cto", RelationshipChannel.TRUST, 0.9)
    network.set_relationship("dev1", "cto", RelationshipChannel.INFLUENCE, 0.5)
    network.set_relationship("dev1", "cto", RelationshipChannel.REPORTING, 0.7)
    
    # CEO <-> Design: Creative tension
    network.set_relationship("ceo", "design", RelationshipChannel.COLLABORATION, 0.5)
    network.set_relationship("ceo", "design", RelationshipChannel.TRUST, 0.6)
    network.set_relationship("ceo", "design", RelationshipChannel.COMMUNICATION, -0.3)  # Communication gap
    
    network.set_relationship("design", "ceo", RelationshipChannel.TRUST, 0.5)
    network.set_relationship("design", "ceo", RelationshipChannel.INFLUENCE, -0.4)  # Feels unheard
    
    # Design <-> Dev: Good working relationship
    network.set_relationship("design", "dev1", RelationshipChannel.COLLABORATION, 0.7)
    network.set_relationship("design", "dev1", RelationshipChannel.COMMUNICATION, 0.75)
    network.set_relationship("design", "dev1", RelationshipChannel.SOCIAL, 0.5)
    
    network.set_relationship("dev1", "design", RelationshipChannel.COLLABORATION, 0.7)
    network.set_relationship("dev1", "design", RelationshipChannel.TRUST, 0.6)
    
    # CFO is somewhat isolated
    network.set_relationship("cfo", "cto", RelationshipChannel.COMMUNICATION, 0.3)
    network.set_relationship("cfo", "dev1", RelationshipChannel.COMMUNICATION, 0.2)
    
    return network


def create_corporate_team() -> OrganizationalNetwork:
    """
    Create a larger corporate team with hierarchical dynamics.
    
    Scenario: Established corporate team with clear hierarchy
    but some cross-functional friction.
    """
    network = OrganizationalNetwork("Corporate Project Team")
    
    members = [
        TeamMember("vp", "Patricia Williams", "VP Engineering", "Engineering"),
        TeamMember("mgr1", "Robert Kim", "Engineering Manager", "Engineering"),
        TeamMember("mgr2", "Sarah Johnson", "Product Manager", "Product"),
        TeamMember("sr1", "Michael Brown", "Senior Engineer", "Engineering"),
        TeamMember("sr2", "Lisa Garcia", "Senior Engineer", "Engineering"),
        TeamMember("jr1", "James Wilson", "Junior Engineer", "Engineering"),
        TeamMember("jr2", "Emily Davis", "Junior Engineer", "Engineering"),
        TeamMember("qa", "David Martinez", "QA Lead", "Quality"),
    ]
    
    for m in members:
        network.add_member(m)
    
    # VP -> Managers: Strong leadership
    network.set_relationship("vp", "mgr1", RelationshipChannel.TRUST, 0.8)
    network.set_relationship("vp", "mgr1", RelationshipChannel.INFLUENCE, 0.9)
    network.set_relationship("vp", "mgr1", RelationshipChannel.COMMUNICATION, 0.7)
    
    network.set_relationship("vp", "mgr2", RelationshipChannel.TRUST, 0.7)
    network.set_relationship("vp", "mgr2", RelationshipChannel.COMMUNICATION, 0.75)
    network.set_relationship("vp", "mgr2", RelationshipChannel.COLLABORATION, 0.6)
    
    # Managers -> VP
    network.set_relationship("mgr1", "vp", RelationshipChannel.REPORTING, 0.9)
    network.set_relationship("mgr1", "vp", RelationshipChannel.TRUST, 0.75)
    network.set_relationship("mgr2", "vp", RelationshipChannel.REPORTING, 0.85)
    network.set_relationship("mgr2", "vp", RelationshipChannel.TRUST, 0.7)
    
    # Eng Manager <-> Product Manager: CONFLICT (classic tension)
    network.set_relationship("mgr1", "mgr2", RelationshipChannel.COLLABORATION, 0.6)
    network.set_relationship("mgr1", "mgr2", RelationshipChannel.TRUST, -0.3)  # Doesn't trust priorities
    network.set_relationship("mgr1", "mgr2", RelationshipChannel.COMMUNICATION, 0.4)
    
    network.set_relationship("mgr2", "mgr1", RelationshipChannel.COLLABORATION, 0.5)
    network.set_relationship("mgr2", "mgr1", RelationshipChannel.TRUST, -0.2)
    network.set_relationship("mgr2", "mgr1", RelationshipChannel.INFLUENCE, -0.4)  # Feels blocked
    
    # Manager -> Senior Engineers
    network.set_relationship("mgr1", "sr1", RelationshipChannel.TRUST, 0.85)
    network.set_relationship("mgr1", "sr1", RelationshipChannel.COLLABORATION, 0.8)
    network.set_relationship("mgr1", "sr1", RelationshipChannel.INFLUENCE, 0.7)
    
    network.set_relationship("mgr1", "sr2", RelationshipChannel.TRUST, 0.7)
    network.set_relationship("mgr1", "sr2", RelationshipChannel.COLLABORATION, 0.65)
    
    # Senior Engineers
    network.set_relationship("sr1", "mgr1", RelationshipChannel.REPORTING, 0.8)
    network.set_relationship("sr1", "mgr1", RelationshipChannel.TRUST, 0.8)
    network.set_relationship("sr2", "mgr1", RelationshipChannel.REPORTING, 0.75)
    network.set_relationship("sr2", "mgr1", RelationshipChannel.TRUST, 0.65)
    
    # Senior <-> Senior: Some rivalry
    network.set_relationship("sr1", "sr2", RelationshipChannel.COLLABORATION, 0.5)
    network.set_relationship("sr1", "sr2", RelationshipChannel.TRUST, 0.4)
    network.set_relationship("sr1", "sr2", RelationshipChannel.INFLUENCE, -0.2)  # Competition
    
    network.set_relationship("sr2", "sr1", RelationshipChannel.COLLABORATION, 0.45)
    network.set_relationship("sr2", "sr1", RelationshipChannel.TRUST, 0.35)
    network.set_relationship("sr2", "sr1", RelationshipChannel.INFLUENCE, -0.3)
    
    # Seniors -> Juniors (mentoring)
    network.set_relationship("sr1", "jr1", RelationshipChannel.INFLUENCE, 0.8)
    network.set_relationship("sr1", "jr1", RelationshipChannel.TRUST, 0.7)
    network.set_relationship("sr1", "jr1", RelationshipChannel.COLLABORATION, 0.6)
    
    network.set_relationship("sr2", "jr2", RelationshipChannel.INFLUENCE, 0.75)
    network.set_relationship("sr2", "jr2", RelationshipChannel.TRUST, 0.65)
    
    # Juniors -> Seniors
    network.set_relationship("jr1", "sr1", RelationshipChannel.TRUST, 0.85)
    network.set_relationship("jr1", "sr1", RelationshipChannel.INFLUENCE, 0.4)
    network.set_relationship("jr2", "sr2", RelationshipChannel.TRUST, 0.7)
    
    # Junior peers
    network.set_relationship("jr1", "jr2", RelationshipChannel.SOCIAL, 0.8)
    network.set_relationship("jr1", "jr2", RelationshipChannel.COLLABORATION, 0.7)
    network.set_relationship("jr1", "jr2", RelationshipChannel.TRUST, 0.75)
    
    network.set_relationship("jr2", "jr1", RelationshipChannel.SOCIAL, 0.85)
    network.set_relationship("jr2", "jr1", RelationshipChannel.TRUST, 0.8)
    
    # QA relationships (often challenging)
    network.set_relationship("qa", "mgr1", RelationshipChannel.COMMUNICATION, 0.6)
    network.set_relationship("qa", "mgr1", RelationshipChannel.TRUST, 0.7)
    
    network.set_relationship("qa", "sr1", RelationshipChannel.COLLABORATION, 0.5)
    network.set_relationship("qa", "sr1", RelationshipChannel.TRUST, -0.2)  # Friction over bugs
    
    network.set_relationship("qa", "sr2", RelationshipChannel.COLLABORATION, 0.4)
    network.set_relationship("qa", "sr2", RelationshipChannel.COMMUNICATION, 0.5)
    
    network.set_relationship("sr1", "qa", RelationshipChannel.COLLABORATION, 0.4)
    network.set_relationship("sr1", "qa", RelationshipChannel.TRUST, -0.1)
    
    # Product manager & QA
    network.set_relationship("mgr2", "qa", RelationshipChannel.COLLABORATION, 0.7)
    network.set_relationship("mgr2", "qa", RelationshipChannel.TRUST, 0.6)
    network.set_relationship("qa", "mgr2", RelationshipChannel.TRUST, 0.65)
    
    return network


def create_remote_team() -> OrganizationalNetwork:
    """
    Create a remote/distributed team with communication challenges.
    
    Scenario: Fully remote team spread across timezones with
    varying levels of async communication effectiveness.
    """
    network = OrganizationalNetwork("Remote Distributed Team")
    
    members = [
        TeamMember("lead_us", "Jennifer Smith", "Team Lead (US)", "Engineering"),
        TeamMember("dev_us", "Mike Johnson", "Developer (US)", "Engineering"),
        TeamMember("dev_eu", "Anna Mueller", "Developer (EU)", "Engineering"),
        TeamMember("dev_asia", "Wei Zhang", "Developer (Asia)", "Engineering"),
        TeamMember("pm", "Carlos Rodriguez", "Product Manager (LATAM)", "Product"),
    ]
    
    for m in members:
        network.add_member(m)
    
    # US Lead <-> US Dev: Strong same-timezone bond
    network.set_relationship("lead_us", "dev_us", RelationshipChannel.COLLABORATION, 0.85)
    network.set_relationship("lead_us", "dev_us", RelationshipChannel.COMMUNICATION, 0.9)
    network.set_relationship("lead_us", "dev_us", RelationshipChannel.TRUST, 0.8)
    network.set_relationship("lead_us", "dev_us", RelationshipChannel.SOCIAL, 0.7)
    
    network.set_relationship("dev_us", "lead_us", RelationshipChannel.TRUST, 0.85)
    network.set_relationship("dev_us", "lead_us", RelationshipChannel.REPORTING, 0.8)
    network.set_relationship("dev_us", "lead_us", RelationshipChannel.SOCIAL, 0.65)
    
    # US Lead <-> EU Dev: Good but timezone friction
    network.set_relationship("lead_us", "dev_eu", RelationshipChannel.COLLABORATION, 0.6)
    network.set_relationship("lead_us", "dev_eu", RelationshipChannel.COMMUNICATION, 0.5)  # Async challenges
    network.set_relationship("lead_us", "dev_eu", RelationshipChannel.TRUST, 0.7)
    
    network.set_relationship("dev_eu", "lead_us", RelationshipChannel.TRUST, 0.65)
    network.set_relationship("dev_eu", "lead_us", RelationshipChannel.COMMUNICATION, 0.4)
    network.set_relationship("dev_eu", "lead_us", RelationshipChannel.INFLUENCE, -0.2)  # Feels excluded from decisions
    
    # US Lead <-> Asia Dev: CONFLICT - timezone causes issues
    network.set_relationship("lead_us", "dev_asia", RelationshipChannel.COLLABORATION, 0.4)
    network.set_relationship("lead_us", "dev_asia", RelationshipChannel.COMMUNICATION, -0.3)  # Poor sync
    network.set_relationship("lead_us", "dev_asia", RelationshipChannel.TRUST, 0.5)
    
    network.set_relationship("dev_asia", "lead_us", RelationshipChannel.TRUST, 0.45)
    network.set_relationship("dev_asia", "lead_us", RelationshipChannel.COMMUNICATION, -0.4)
    network.set_relationship("dev_asia", "lead_us", RelationshipChannel.INFLUENCE, -0.5)  # Feels very isolated
    
    # EU <-> Asia: Good async workflow
    network.set_relationship("dev_eu", "dev_asia", RelationshipChannel.COLLABORATION, 0.7)
    network.set_relationship("dev_eu", "dev_asia", RelationshipChannel.COMMUNICATION, 0.6)
    network.set_relationship("dev_eu", "dev_asia", RelationshipChannel.TRUST, 0.65)
    
    network.set_relationship("dev_asia", "dev_eu", RelationshipChannel.COLLABORATION, 0.75)
    network.set_relationship("dev_asia", "dev_eu", RelationshipChannel.TRUST, 0.7)
    network.set_relationship("dev_asia", "dev_eu", RelationshipChannel.SOCIAL, 0.4)
    
    # PM relationships (central coordinator)
    network.set_relationship("pm", "lead_us", RelationshipChannel.COLLABORATION, 0.7)
    network.set_relationship("pm", "lead_us", RelationshipChannel.COMMUNICATION, 0.75)
    network.set_relationship("pm", "lead_us", RelationshipChannel.TRUST, 0.6)
    
    network.set_relationship("lead_us", "pm", RelationshipChannel.TRUST, 0.65)
    network.set_relationship("lead_us", "pm", RelationshipChannel.COLLABORATION, 0.6)
    
    network.set_relationship("pm", "dev_eu", RelationshipChannel.COMMUNICATION, 0.65)
    network.set_relationship("pm", "dev_asia", RelationshipChannel.COMMUNICATION, 0.55)
    
    network.set_relationship("dev_eu", "pm", RelationshipChannel.TRUST, 0.6)
    network.set_relationship("dev_asia", "pm", RelationshipChannel.TRUST, 0.5)
    
    # US Dev has limited cross-TZ connections (relies on lead)
    network.set_relationship("dev_us", "dev_eu", RelationshipChannel.COLLABORATION, 0.4)
    network.set_relationship("dev_us", "dev_asia", RelationshipChannel.COLLABORATION, 0.25)
    
    return network


def create_consulting_team() -> OrganizationalNetwork:
    """
    Create a consulting/professional services team.
    
    Scenario: Project-based team with client interface
    and strong senior/junior dynamics.
    """
    network = OrganizationalNetwork("Consulting Project Team")
    
    members = [
        TeamMember("partner", "Elizabeth Warren", "Partner", "Leadership"),
        TeamMember("mgr", "Thomas Chen", "Engagement Manager", "Delivery"),
        TeamMember("cons1", "Rachel Green", "Senior Consultant", "Delivery"),
        TeamMember("cons2", "Daniel Park", "Consultant", "Delivery"),
        TeamMember("analyst", "Sophia Martinez", "Analyst", "Delivery"),
    ]
    
    for m in members:
        network.add_member(m)
    
    # Partner -> Manager: High trust, clear expectations
    network.set_relationship("partner", "mgr", RelationshipChannel.TRUST, 0.9)
    network.set_relationship("partner", "mgr", RelationshipChannel.INFLUENCE, 0.85)
    network.set_relationship("partner", "mgr", RelationshipChannel.COMMUNICATION, 0.8)
    
    network.set_relationship("mgr", "partner", RelationshipChannel.REPORTING, 0.9)
    network.set_relationship("mgr", "partner", RelationshipChannel.TRUST, 0.85)
    network.set_relationship("mgr", "partner", RelationshipChannel.INFLUENCE, 0.5)
    
    # Manager -> Senior: Working partnership
    network.set_relationship("mgr", "cons1", RelationshipChannel.COLLABORATION, 0.85)
    network.set_relationship("mgr", "cons1", RelationshipChannel.TRUST, 0.8)
    network.set_relationship("mgr", "cons1", RelationshipChannel.COMMUNICATION, 0.75)
    
    network.set_relationship("cons1", "mgr", RelationshipChannel.TRUST, 0.8)
    network.set_relationship("cons1", "mgr", RelationshipChannel.REPORTING, 0.7)
    network.set_relationship("cons1", "mgr", RelationshipChannel.INFLUENCE, 0.4)
    
    # Manager -> Consultant: Development focus
    network.set_relationship("mgr", "cons2", RelationshipChannel.TRUST, 0.65)
    network.set_relationship("mgr", "cons2", RelationshipChannel.INFLUENCE, 0.7)
    network.set_relationship("mgr", "cons2", RelationshipChannel.COLLABORATION, 0.6)
    
    network.set_relationship("cons2", "mgr", RelationshipChannel.TRUST, 0.7)
    network.set_relationship("cons2", "mgr", RelationshipChannel.REPORTING, 0.8)
    
    # Senior -> Consultant: CONFLICT - workload tension
    network.set_relationship("cons1", "cons2", RelationshipChannel.COLLABORATION, 0.55)
    network.set_relationship("cons1", "cons2", RelationshipChannel.TRUST, -0.2)  # Performance concerns
    network.set_relationship("cons1", "cons2", RelationshipChannel.INFLUENCE, 0.6)
    
    network.set_relationship("cons2", "cons1", RelationshipChannel.TRUST, 0.4)
    network.set_relationship("cons2", "cons1", RelationshipChannel.INFLUENCE, -0.3)  # Feels micromanaged
    network.set_relationship("cons2", "cons1", RelationshipChannel.SOCIAL, 0.3)
    
    # Senior -> Analyst: Strong mentorship
    network.set_relationship("cons1", "analyst", RelationshipChannel.INFLUENCE, 0.8)
    network.set_relationship("cons1", "analyst", RelationshipChannel.TRUST, 0.7)
    network.set_relationship("cons1", "analyst", RelationshipChannel.COLLABORATION, 0.75)
    
    network.set_relationship("analyst", "cons1", RelationshipChannel.TRUST, 0.85)
    network.set_relationship("analyst", "cons1", RelationshipChannel.REPORTING, 0.6)
    network.set_relationship("analyst", "cons1", RelationshipChannel.SOCIAL, 0.5)
    
    # Consultant -> Analyst: Peer support
    network.set_relationship("cons2", "analyst", RelationshipChannel.SOCIAL, 0.7)
    network.set_relationship("cons2", "analyst", RelationshipChannel.COLLABORATION, 0.6)
    network.set_relationship("cons2", "analyst", RelationshipChannel.TRUST, 0.65)
    
    network.set_relationship("analyst", "cons2", RelationshipChannel.SOCIAL, 0.75)
    network.set_relationship("analyst", "cons2", RelationshipChannel.TRUST, 0.7)
    
    # Manager -> Analyst: Direct line
    network.set_relationship("mgr", "analyst", RelationshipChannel.INFLUENCE, 0.6)
    network.set_relationship("mgr", "analyst", RelationshipChannel.TRUST, 0.55)
    
    network.set_relationship("analyst", "mgr", RelationshipChannel.REPORTING, 0.75)
    network.set_relationship("analyst", "mgr", RelationshipChannel.TRUST, 0.6)
    
    # Partner occasionally interacts directly
    network.set_relationship("partner", "cons1", RelationshipChannel.TRUST, 0.7)
    network.set_relationship("partner", "cons1", RelationshipChannel.INFLUENCE, 0.75)
    
    network.set_relationship("cons1", "partner", RelationshipChannel.TRUST, 0.75)
    network.set_relationship("cons1", "partner", RelationshipChannel.INFLUENCE, 0.3)
    
    return network


def get_sample_datasets():
    """Return dictionary of all available sample datasets."""
    return {
        "Engineering Team (Default)": create_sample_network,
        "Startup Founding Team": create_startup_team,
        "Corporate Project Team": create_corporate_team,
        "Remote Distributed Team": create_remote_team,
        "Consulting Project Team": create_consulting_team,
    }


# Import the default sample for backward compatibility
from org_analysis import create_sample_network
