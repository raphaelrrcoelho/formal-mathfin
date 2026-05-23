"""Allow running as `python -m python.cli`."""
from .cli import main
raise SystemExit(main())
