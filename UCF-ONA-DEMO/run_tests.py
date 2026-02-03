#!/usr/bin/env python3
"""
Run UCF/GUTT unit tests.

Usage:
    python run_tests.py           # Run all tests
    python run_tests.py -v        # Verbose output
"""

import subprocess
import sys
import os

def check_pytest():
    """Check if pytest is available."""
    try:
        import pytest
        return True
    except ImportError:
        return False

def main():
    # Ensure we're in the right directory
    script_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(script_dir)
    
    print("=" * 60)
    print("UCF/GUTT Unit Test Runner")
    print("=" * 60)
    
    if check_pytest():
        # Use pytest if available
        cmd = [sys.executable, "-m", "pytest", "tests/", "-v", "--tb=short"]
        cmd.extend(sys.argv[1:])
        print(f"Running with pytest: {' '.join(cmd)}")
    else:
        # Fallback to unittest
        cmd = [sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"]
        print(f"Running with unittest (pytest not installed): {' '.join(cmd)}")
    
    print()
    
    # Run tests
    result = subprocess.run(cmd)
    
    print()
    print("=" * 60)
    if result.returncode == 0:
        print("✅ All tests passed!")
    else:
        print(f"❌ Tests failed with return code {result.returncode}")
    print("=" * 60)
    
    return result.returncode


if __name__ == "__main__":
    sys.exit(main())
