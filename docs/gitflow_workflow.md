# Gitflow Workflow

This document outlines the standard Gitflow workflow rules for this environment, emphasizing frequent integration and automated verification.

## Branch Strategy

| Branch | Purpose | Push Frequency |
| --- | --- | --- |
| `develop` | Daily hotfixes, features, and active development | Throughout the day (frequent) |
| `main` | Production releases only | End of day / release |
| `staging` | Pre-release testing | Optional |

## Daily Workflow

**During the day (Active Development):**
Work strictly on the `develop` branch. Push your changes frequently to ensure continuous integration and verification.
```bash
# Work on develop, push frequently
git add .
git commit -m "fix: description"
git push origin develop
```
*Note: CI runs tests automatically upon pushes to develop.*

**End of day (Release):**
Only when all tests pass and the code is ready for release, merge `develop` into `main` and tag the release.
```bash
git checkout main
git merge develop
git tag vX.Y.Z
git push origin main --tags
```
*Note: Tags trigger release builds via GitHub Actions.*

## Critical Rules

- ❌ **Never push directly to `main`.** Always merge from `develop`.
- ✅ **Push to `develop` first,** let CI verify your changes.
- ✅ **Only merge to `main`** when tests pass and you are ready for a release.
- ✅ **Tags trigger release builds** via GitHub Actions.
- ✅ **Set upstream tracking:** `git branch --set-upstream-to=origin/develop develop`
