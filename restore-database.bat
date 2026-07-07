@echo off
setlocal

echo ============================================================
echo  Restore proofsearch database from the pre-rename chatdb.db
echo ============================================================
echo.
echo IMPORTANT: Quit Claude Code completely BEFORE running this.
echo The server must not have chatdb.db or proofsearch.db open,
echo or the rename below will fail.
echo.
pause

cd /d "%~dp0"

if not exist "chatdb.db" (
    echo.
    echo ERROR: chatdb.db not found in this folder. Nothing to restore.
    echo   ^(If you already restored it, you're done - just relaunch Claude Code.^)
    goto :end
)

echo.
echo Found chatdb.db - this is the real data, about to become proofsearch.db
echo.

if exist "proofsearch.db" (
    echo Removing the empty placeholder proofsearch.db and its sidecar files...
    del /f /q "proofsearch.db" 2>nul
    del /f /q "proofsearch.db-shm" 2>nul
    del /f /q "proofsearch.db-wal" 2>nul
)

echo Renaming chatdb.db -^> proofsearch.db ...
ren "chatdb.db" "proofsearch.db"
if errorlevel 1 (
    echo.
    echo FAILED to rename chatdb.db. Is Claude Code still running?
    echo Quit it fully and run this file again.
    goto :end
)

if exist "chatdb.db-shm" (
    ren "chatdb.db-shm" "proofsearch.db-shm"
)
if exist "chatdb.db-wal" (
    ren "chatdb.db-wal" "proofsearch.db-wal"
)

echo.
echo ============================================================
echo  Done. Your tracked history is now at proofsearch.db.
echo  You can relaunch Claude Code.
echo ============================================================

:end
echo.
pause
