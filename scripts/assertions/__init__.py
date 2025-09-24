"""
Assertion generation plugin package.

How to add a new assertion type (plugin):
- Create a new module file in this package (e.g., my_assertion.py).
- Implement a class derived from BaseAssertionPlugin.
- Define:
  - plugin_name: short identifier (e.g., "counter").
  - sheet_name: Excel sheet name that this plugin consumes.
  - parse(xls_path): read the sheet and return a structured dict.
  - generate_sv(parsed, context): return a list of SV section strings.
- Register the plugin class in registry.py (PLUGINS list) or expose
  a function plugins() in your module that returns [YourPlugin].

Assistant usage hint (for future AI extension requests):
- "Add a plugin for sheet 'my_new_gen' with headers X,Y,Z that should
   generate property templates P; map X->A, Y->B logic as ..."
  The AI should implement a new plugin following BaseAssertionPlugin
  and hook it in registry.PLUGINS.
"""

from .base import BaseAssertionPlugin
from .registry import get_registered_plugins

__all__ = [
    "BaseAssertionPlugin",
    "get_registered_plugins",
]


