import readline from 'node:readline/promises';
import { stdin as input, stdout as output } from 'node:process';

const AUTOMATED_ENV_VARS = [
  'CI',
  'CLAUDECODE',
  'CURSOR_AGENT',
  'CODEX_CI',
  'OPENCODE',
  'AMP_HOME',
  'AMI',
];

export function isAutomatedEnvironment(): boolean {
  return AUTOMATED_ENV_VARS.some((name) => Boolean(process.env[name]));
}

export function shouldSkipPrompts(yesFlag: boolean): boolean {
  return yesFlag || isAutomatedEnvironment() || !process.stdin.isTTY;
}

export async function confirmPrompt(message: string, defaultYes = true): Promise<boolean> {
  if (!process.stdin.isTTY) {
    return false;
  }

  const suffix = defaultYes ? ' [Y/n] ' : ' [y/N] ';
  const rl = readline.createInterface({ input, output });

  try {
    const raw = await rl.question(`${message}${suffix}`);
    const answer = raw.trim().toLowerCase();

    if (!answer) {
      return defaultYes;
    }

    if (answer === 'y' || answer === 'yes') {
      return true;
    }

    if (answer === 'n' || answer === 'no') {
      return false;
    }

    return defaultYes;
  } finally {
    rl.close();
  }
}
