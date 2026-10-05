# Park That Thought installer for Windows. No admin needed.
# Run:  powershell -c "irm https://raw.githubusercontent.com/gmiqbal/ParkThatThought/main/install.ps1 | Out-String | iex"
# Running it again updates the app. Your notes (parking_lot_data) are never touched.
& {
    $ProgressPreference = "SilentlyContinue"
    [Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12
    $repo = "https://raw.githubusercontent.com/gmiqbal/ParkThatThought/main"
    $dir = Join-Path $env:LOCALAPPDATA "ParkThatThought"
    $script = Join-Path $dir "parking_lot.py"
    $venv = Join-Path $dir "venv"

    function Find-Python {
        $probe = "import sys; print(sys.executable if sys.version_info >= (3, 9) else '')"
        # "command|first argument"; the folder check catches a Python that winget just installed without PATH
        $tries = @("py|-3", "python|", "python3|") + @(Get-ChildItem "$env:LOCALAPPDATA\Programs\Python\Python3*\python.exe" `
            -ErrorAction SilentlyContinue | ForEach-Object { "$($_.FullName)|" })
        foreach ($t in $tries) {
            $exe, $first = $t.Split("|")
            if (-not (Get-Command $exe -ErrorAction SilentlyContinue)) { continue }
            $extra = @($first | Where-Object { $_ })
            $out = & $exe @extra -c $probe 2>$null | Select-Object -Last 1
            if ($out -and (Test-Path $out)) { return $out }
        }
    }

    Write-Host "Installing Park That Thought into $dir"
    New-Item -ItemType Directory -Force $dir | Out-Null

    $py = Find-Python
    if (-not $py -and (Get-Command winget -ErrorAction SilentlyContinue)) {
        Write-Host "Python not found. Installing Python 3.12 with winget (one time)..."
        winget install -e --id Python.Python.3.12 --scope user --accept-package-agreements --accept-source-agreements
        $env:Path = [Environment]::GetEnvironmentVariable("Path", "User") + ";" + [Environment]::GetEnvironmentVariable("Path", "Machine")
        $py = Find-Python
    }
    if (-not $py) {
        Write-Host "Couldn't find or install Python 3.9 or newer." -ForegroundColor Red
        Write-Host "Get it from https://www.python.org/downloads/ (tick 'Add python.exe to PATH'), then run this again."
        return
    }
    Write-Host "Using Python: $py"

    $vpy = Join-Path $venv "Scripts\python.exe"
    $vpyw = Join-Path $venv "Scripts\pythonw.exe"
    if (-not (Test-Path $vpyw)) {
        Write-Host "Making a private Python environment for the app..."
        & $py -m venv $venv
    }
    Write-Host "Installing PySide6 and pynput (about 200 MB the first time)..."
    & $vpy -m pip install --disable-pip-version-check --quiet "PySide6>=6.5" "pynput>=1.7"
    if ($LASTEXITCODE -ne 0 -or -not (Test-Path $vpyw)) {
        Write-Host "Installing the libraries failed. Check your internet connection and run this again." -ForegroundColor Red
        Write-Host "If it keeps failing, install Python 3.12 from python.org, delete $venv and run this again."
        return
    }

    Write-Host "Downloading the app..."
    try {
        Invoke-WebRequest "$repo/parking_lot.py" -OutFile "$script.new" -UseBasicParsing
        Move-Item -Force "$script.new" $script
    } catch {
        Write-Host "Download failed: $($_.Exception.Message)" -ForegroundColor Red
        return
    }

    $shell = New-Object -ComObject WScript.Shell
    foreach ($folder in [Environment]::GetFolderPath("Programs"), [Environment]::GetFolderPath("Startup")) {
        $lnk = $shell.CreateShortcut((Join-Path $folder "Park That Thought.lnk"))
        $lnk.TargetPath = $vpyw
        $lnk.Arguments = "`"$script`""
        $lnk.WorkingDirectory = $dir
        $lnk.Description = "Park stray thoughts during focus"
        $lnk.Save()
    }

    # --replace hands over from a copy that is already running, so a re-install picks up the new version
    Start-Process $vpyw -ArgumentList "`"$script`"", "--replace" -WorkingDirectory $dir
    Write-Host ""
    Write-Host "Done. Look for the cloud on the right edge of your screen." -ForegroundColor Green
    Write-Host "Ctrl+Alt+P parks a thought, Ctrl+Alt+L opens the list. It also starts with Windows."
}
