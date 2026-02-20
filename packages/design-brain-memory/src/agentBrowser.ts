import { spawn, spawnSync } from 'node:child_process';

export interface AgentBrowserJsonResponse {
  success: boolean;
  data: Record<string, unknown>;
  error: string | null;
}

interface RunnerConfig {
  command: string;
  prefixArgs: string[];
}

let cachedRunner: RunnerConfig | null = null;

function canExecute(command: string, args: string[]): boolean {
  const result = spawnSync(command, args, {
    stdio: 'ignore',
    env: {
      ...process.env,
      NPM_CONFIG_UPDATE_NOTIFIER: 'false',
      npm_config_update_notifier: 'false',
    },
  });
  return result.status === 0;
}

function resolveRunner(): RunnerConfig {
  if (cachedRunner) {
    return cachedRunner;
  }

  const fromEnv = process.env.DESIGN_BRAIN_AGENT_BROWSER_BIN;
  if (fromEnv && canExecute(fromEnv, ['--version'])) {
    cachedRunner = { command: fromEnv, prefixArgs: [] };
    return cachedRunner;
  }

  if (canExecute('agent-browser', ['--version'])) {
    cachedRunner = { command: 'agent-browser', prefixArgs: [] };
    return cachedRunner;
  }

  cachedRunner = { command: 'npx', prefixArgs: ['--yes', 'agent-browser'] };
  return cachedRunner;
}

function parseJsonFromOutput(stdout: string): AgentBrowserJsonResponse {
  const lines = stdout
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0);

  for (let i = lines.length - 1; i >= 0; i -= 1) {
    const line = lines[i];
    if (!line.startsWith('{') || !line.endsWith('}')) {
      continue;
    }

    try {
      const parsed = JSON.parse(line) as AgentBrowserJsonResponse;
      if (typeof parsed.success === 'boolean') {
        return parsed;
      }
    } catch {
      // keep searching
    }
  }

  throw new Error(`Failed to parse Agent Browser JSON response. Output:\n${stdout}`);
}

export async function runAgentBrowserJson(
  args: string[],
  options: { session?: string; cwd?: string; headed?: boolean } = {}
): Promise<AgentBrowserJsonResponse> {
  const runner = resolveRunner();
  const finalArgs = [
    ...runner.prefixArgs,
    ...(options.session ? ['--session', options.session] : []),
    ...(options.headed ? ['--headed'] : []),
    '--json',
    ...args,
  ];

  return new Promise<AgentBrowserJsonResponse>((resolve, reject) => {
    const child = spawn(runner.command, finalArgs, {
      cwd: options.cwd,
      env: {
        ...process.env,
        NPM_CONFIG_UPDATE_NOTIFIER: 'false',
        npm_config_update_notifier: 'false',
      },
      stdio: ['ignore', 'pipe', 'pipe'],
    });

    let stdout = '';
    let stderr = '';

    child.stdout.on('data', (chunk: Buffer | string) => {
      stdout += chunk.toString();
    });

    child.stderr.on('data', (chunk: Buffer | string) => {
      stderr += chunk.toString();
    });

    child.on('error', (error) => {
      reject(error);
    });

    child.on('close', (code) => {
      if (code !== 0) {
        reject(new Error(`agent-browser command failed (${code}): ${stderr || stdout}`));
        return;
      }

      try {
        resolve(parseJsonFromOutput(stdout));
      } catch (error) {
        const details = stderr ? `${(error as Error).message}\n${stderr}` : (error as Error).message;
        reject(new Error(details));
      }
    });
  });
}
