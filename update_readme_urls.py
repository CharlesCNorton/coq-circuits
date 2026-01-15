"""
Update all README files to use -verified instead of -prover
"""

import os
import glob

def update_file(filepath):
    """Replace -prover with -verified in a file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        original_content = content
        content = content.replace('-prover', '-verified')

        if content != original_content:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            return True
        return False
    except Exception as e:
        print(f"  [ERROR] {filepath}: {e}")
        return False

# Find all README files
readme_files = []
readme_files.extend(glob.glob('weights/**/*README.md', recursive=True))
readme_files.append('README.md')

print("=" * 70)
print("Updating README URLs: -prover to -verified")
print("=" * 70)

updated_count = 0
for filepath in readme_files:
    if os.path.exists(filepath):
        if update_file(filepath):
            print(f"[UPDATED] {filepath}")
            updated_count += 1
        else:
            print(f"[SKIPPED] {filepath} (no changes needed)")

print("\n" + "=" * 70)
print(f"Update Complete: {updated_count} files updated")
print("=" * 70)
