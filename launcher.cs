// QuickSearch launcher: starts QuickSearch.pyw (next to this .exe) with pythonw and exits.
// Exists so QuickSearch can be pinned to the taskbar / Start like a normal program.
// Build:  csc /nologo /target:winexe /win32icon:QuickSearch.ico /out:QuickSearch.exe launcher.cs
using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Windows.Forms;

static class Launcher
{
    static string FindPythonw()
    {
        // 1) pythonw.exe on PATH
        foreach (var dir in (Environment.GetEnvironmentVariable("PATH") ?? "").Split(';'))
        {
            try
            {
                var p = Path.Combine(dir.Trim().Trim('"'), "pythonw.exe");
                if (dir.Trim().Length > 0 && File.Exists(p) && !p.ToLower().Contains("windowsapps")) return p;
            }
            catch (ArgumentException) { }
        }
        // 2) per-user / all-users python.org installs, newest first
        var roots = new[] {
            Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "Programs", "Python"),
            Environment.GetFolderPath(Environment.SpecialFolder.ProgramFiles),
        };
        foreach (var root in roots.Where(Directory.Exists))
        {
            var found = Directory.GetDirectories(root, "Python3*")
                .OrderByDescending(d => d, StringComparer.OrdinalIgnoreCase)
                .Select(d => Path.Combine(d, "pythonw.exe"))
                .FirstOrDefault(File.Exists);
            if (found != null) return found;
        }
        // 3) the py launcher's windowed variant
        var pyw = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.Windows), "pyw.exe");
        return File.Exists(pyw) ? pyw : null;
    }

    [STAThread]
    static int Main(string[] args)
    {
        var dir = AppDomain.CurrentDomain.BaseDirectory;
        var script = Path.Combine(dir, "QuickSearch.pyw");
        if (!File.Exists(script))
        {
            MessageBox.Show("QuickSearch.pyw was not found next to this program:\n" + script, "QuickSearch",
                            MessageBoxButtons.OK, MessageBoxIcon.Error);
            return 1;
        }
        var pythonw = FindPythonw();
        if (pythonw == null)
        {
            MessageBox.Show("Python (pythonw.exe) was not found.\nInstall Python 3 from python.org and try again.",
                            "QuickSearch", MessageBoxButtons.OK, MessageBoxIcon.Error);
            return 1;
        }
        var argLine = "\"" + script + "\"" + string.Concat(args.Select(a => " \"" + a.Replace("\"", "\\\"") + "\""));
        var psi = new ProcessStartInfo(pythonw, argLine) { WorkingDirectory = dir, UseShellExecute = false };
        try { Process.Start(psi); }
        catch (Exception ex)
        {
            MessageBox.Show("Could not start QuickSearch:\n" + ex.Message, "QuickSearch",
                            MessageBoxButtons.OK, MessageBoxIcon.Error);
            return 1;
        }
        return 0;
    }
}
