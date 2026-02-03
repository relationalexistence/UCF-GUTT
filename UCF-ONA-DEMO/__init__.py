"""
UCF/GUTT Organizational Network Analysis - DEMO VERSION
=========================================================

Copyright (c) 2024 Michael Fillippini. All Rights Reserved.

DEMONSTRATION ONLY - Simplified algorithms for concept illustration.

Production system available at: https://relationalexistence.com
Contact: Michael_Fill@ProtonMail.com
"""

__copyright__ = "Copyright (c) 2024 Michael Fillippini. All Rights Reserved."
__license__ = "Proprietary - Demo Only"
__version__ = "DEMO-1.0"
__author__ = "Michael Fillippini"

from .ucf_core import (
    RelationSign,
    WeightedEdge,
    WeightedRelation,
    MultiplexRelation,
    ConflictReport,
    HostileReport,
    HarmonyReport,
)

from .org_analysis import (
    RelationshipChannel,
    TeamMember,
    TeamHealthReport,
    OrganizationalNetwork,
    get_license_notice,
)
